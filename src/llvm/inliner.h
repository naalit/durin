#include "llvm/IR/PassManager.h"

/// Inlines functions with the "inline-late" attribute, after RewriteStatepointsForGC.
/// Those functions should also be "gc-leaf-function"s so they can survive RS4GC,
/// `noinline` so they don't get inlined too early ("inline-late" doesn't do this),
/// and `private` so they can be deleted after.
class Inliner : public llvm::PassInfoMixin<Inliner> {
public:
  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &);
  static bool isRequired() { return true; }
};