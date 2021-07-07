#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Bitcode/BitcodeWriterPass.h"
#include "llvm/Transforms/Scalar/RewriteStatepointsForGC.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/IR/IRPrintingPasses.h"

#include "inliner.h"
#include "tailerizer.h"

using namespace llvm;

extern "C" int do_opt(const char *bitcode, size_t bitcode_len, const char *filename, const char *out_file, bool optimize) {
    // Load the module
    LLVMContext context;
    SMDiagnostic Err;

    auto buf = MemoryBuffer::getMemBuffer(StringRef(bitcode, bitcode_len), filename);

    std::unique_ptr<Module> mod = parseIR(*buf, Err, context);

    if (!mod) {
        Err.print(filename, errs());
        return 1;
    }

    if (verifyModule(*mod, &errs())) {
        errs() << "input module is broken\n";
        return 1;
    }

    // Run optimizations
    LoopAnalysisManager LAM;
    FunctionAnalysisManager FAM;
    CGSCCAnalysisManager CGAM;
    ModuleAnalysisManager MAM;

    PassBuilder PB;
    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

    ModulePassManager MPM = PB.buildPerModuleDefaultPipeline(optimize
        ? PassBuilder::OptimizationLevel::O3
        : PassBuilder::OptimizationLevel::O1);

    MPM.addPass(RewriteStatepointsForGC());

    MPM.addPass(Inliner());

    FunctionPassManager FPM;
    FPM.addPass(InstCombinePass());
    #ifdef LLVM_13
    FPM.addPass(Tailerizer(true));
    #else
    FPM.addPass(Tailerizer(false));
    #endif
    MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));

    // MPM.addPass(PrintModulePass());

    MPM.addPass(VerifierPass());

    StringRef OutFile(out_file);
    std::error_code err;
    raw_fd_ostream Out(OutFile, err);
    MPM.addPass(BitcodeWriterPass(Out));

    MPM.run(*mod, MAM);

    return 0;
}