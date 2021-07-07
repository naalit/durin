#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/ProfileSummaryInfo.h"
#include "llvm/IR/Module.h"
#include "llvm/Transforms/IPO/Inliner.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"

#include "inliner.h"

using namespace llvm;

#define DEBUG_TYPE "inline"

// This is mostly copied from the AlwaysInline pass
PreservedAnalyses Inliner::run(Module &M, ModuleAnalysisManager &MAM) {
  // Add inline assumptions during code generation.
  FunctionAnalysisManager &FAM = MAM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();
  auto GetAssumptionCache = [&](Function &F) -> AssumptionCache & {
    return FAM.getResult<AssumptionAnalysis>(F);
  };
  auto &PSI = MAM.getResult<ProfileSummaryAnalysis>(M);

  SmallSetVector<CallBase *, 16> Calls;
  bool Changed = false;
  SmallVector<Function *, 16> InlinedFunctions;
  for (Function &F : M) {
    if (!F.isDeclaration() && F.hasFnAttribute("inline-late") && isInlineViable(F).isSuccess()) {
      Calls.clear();

      for (User *U : F.users())
        if (auto *CB = dyn_cast<CallBase>(U))
          if (CB->getCalledFunction() == &F)
            Calls.insert(CB);

      for (CallBase *CB : Calls) {
        Function *Caller = CB->getCaller();
        OptimizationRemarkEmitter ORE(Caller);
        auto OIC = shouldInline(
            *CB,
            [&](CallBase &) {
              return InlineCost::getAlways("always inline attribute");
            },
            ORE);
        assert(OIC);
        emitInlinedInto(ORE, CB->getDebugLoc(), CB->getParent(), F, *Caller,
                        *OIC, false, DEBUG_TYPE);

        InlineFunctionInfo IFI(
            /*cg=*/nullptr, GetAssumptionCache, &PSI,
            &FAM.getResult<BlockFrequencyAnalysis>(*(CB->getCaller())),
            &FAM.getResult<BlockFrequencyAnalysis>(F));

        InlineResult Res = InlineFunction(
            *CB, IFI, &FAM.getResult<AAManager>(F), true);
        assert(Res.isSuccess() && "unexpected failure to inline");
        (void)Res;

        // Merge the attributes based on the inlining.
        AttributeFuncs::mergeAttributesForInlining(*Caller, F);

        Changed = true;
      }

      // Remember to try and delete this function afterward. This both avoids
      // re-walking the rest of the module and avoids dealing with any iterator
      // invalidation issues while deleting functions.
      InlinedFunctions.push_back(&F);
    }
  }

  // Remove any live functions.
  erase_if(InlinedFunctions, [&](Function *F) {
    F->removeDeadConstantUsers();
    return !F->isDefTriviallyDead();
  });

  // Delete the non-comdat ones from the module and also from our vector.
  auto NonComdatBegin = partition(
      InlinedFunctions, [&](Function *F) { return F->hasComdat(); });
  for (Function *F : make_range(NonComdatBegin, InlinedFunctions.end()))
    M.getFunctionList().erase(F);
  InlinedFunctions.erase(NonComdatBegin, InlinedFunctions.end());

  if (!InlinedFunctions.empty()) {
    // Now we just have the comdat functions. Filter out the ones whose comdats
    // are not actually dead.
    filterDeadComdatFunctions(M, InlinedFunctions);
    // The remaining functions are actually dead.
    for (Function *F : InlinedFunctions)
      M.getFunctionList().erase(F);
  }

  return Changed ? PreservedAnalyses::none() : PreservedAnalyses::all();
}
