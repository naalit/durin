#include "llvm/IR/PassManager.h"

/// Finds tailcc statepoint calls that can be tail calls, and turns them into tail calls.
/// It removes the statepoint and marks the call musttail, which guarantees that nothing 
/// is live after the call so removing the statepoint is safe.
class Tailerizer : public llvm::PassInfoMixin<Tailerizer> {
  bool useMustTail;

public:
  Tailerizer(bool useMustTail) : useMustTail(useMustTail) {}
  llvm::PreservedAnalyses run(llvm::Function &F, llvm::FunctionAnalysisManager &);
  static bool isRequired() { return true; }
};