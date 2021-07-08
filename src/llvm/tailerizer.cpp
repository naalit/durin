#include "llvm/IR/CallingConv.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Statepoint.h"

#include "tailerizer.h"

using namespace llvm;

PreservedAnalyses Tailerizer::run(Function &F, FunctionAnalysisManager &) {
    if (!F.hasGC() || F.getCallingConv() != CallingConv::Tail)
        return PreservedAnalyses::all();

    for (BasicBlock &BB : F) {
        Instruction *Term = BB.getTerminator();

        // Sometimes LLVM creates a common return branch which just returns void.
        // That doesn't let us use `musttail`, so we replace it with a direct return.
        if (auto *Branch = dyn_cast<BranchInst>(Term)) {
            if (Branch->isUnconditional()) {
                auto *NextBB = Branch->getSuccessor(0);
                if (auto *Ret = dyn_cast<ReturnInst>(&NextBB->front())) {
                    if (!Ret->getReturnValue()) {
                        ReturnInst *Ret2 = ReturnInst::Create(Ret->getContext(), nullptr, Branch);
                        Branch->eraseFromParent();
                        if (NextBB->hasNPredecessors(0))
                            NextBB->eraseFromParent();
                        Term = Ret2;
                    }
                }
            }
        }

        // Ignore blocks that don't return
        if (!isa<ReturnInst>(Term))
            continue;

        const GCStatepointInst *STI = nullptr;
        for (auto it = BB.rbegin(); it != BB.rend(); ++it) {
            Instruction &I = *it;
            if (isa<ReturnInst>(I) || isa<BranchInst>(I)) {
                // ignore the return
            } else if (auto *Proj = dyn_cast<GCProjectionInst>(&I)) {
                if (STI == nullptr) {
                    STI = Proj->getStatepoint();
                } else {
                    // Must be from the same statepoint
                    if (STI != Proj->getStatepoint())
                        break;
                }
            } else if (auto *ST = dyn_cast<GCStatepointInst>(&I)) {
                // If we're returning something, it must be from the same statepoint
                if (STI != nullptr && STI != ST)
                    break;
                auto *Ret = cast<ReturnInst>(Term);
                Value *RV = Ret->getReturnValue();
                if (RV == nullptr) {
                    // fine
                } else if (auto *Proj = dyn_cast<GCProjectionInst>(RV)) {
                    if (Proj->getStatepoint() != ST || Proj->getIntrinsicID() != Intrinsic::experimental_gc_result)
                        break;
                } else {
                    // can't return something else if it's a tail call
                    break;
                }

                // It must be a tail call in tailcc
                if (ST->getCallingConv() != CallingConv::Tail || !ST->isTailCall())
                    break;

                // We've checked the conditions, now eliminate the statepoint
                Value *Callee = ST->getActualCalledOperand();
                Type *RetTy = ST->getActualReturnType();
                std::vector<Value*> Args;
                std::vector<Type*> ArgTypes;
                for (const Use &U : ST->actual_args()) {
                    Args.push_back(U.get());
                    ArgTypes.push_back(U.get()->getType());
                }
                FunctionType *CalleeTy = FunctionType::get(RetTy, ArgTypes, false);
                CallInst *Call = CallInst::Create(CalleeTy, Callee, Args);
                Call->setTailCallKind(useMustTail
                    ? CallInst::TailCallKind::TCK_MustTail
                    : CallInst::TailCallKind::TCK_Tail);
                Call->setCallingConv(ST->getCallingConv());
                Call->insertBefore(Ret);

                if (RV != nullptr) {
                    if (RV->hasName()) {
                        auto Name = RV->getName();
                        RV->setName("");
                        Call->setName(Name);
                    }
                    Ret->setOperand(0, Call);
                    cast<Instruction>(RV)->eraseFromParent();
                }
                ST->eraseFromParent();

                break;
            } else {
                // Something else is in the way, it's no longer a tail call
                break;
            }
        }
    }

    return PreservedAnalyses::all();
}