//===----------------------------------------------------------------------------------===//
// LLVM BogusControlFlow Pass
//===----------------------------------------------------------------------------------===//

#include <memory>
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/NoFolder.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Obfuscation/Morphling.h"
#include "llvm/Transforms/Obfuscation/BogusControlFlow.h"

#define DEBUG_TYPE "BogusControlFlow"

using namespace std;
using namespace llvm;

static cl::opt<int>
bcf_rate("mh_bcf_rate",
         cl::desc("don't tell you"),
         cl::value_desc("don't tell you"), cl::init(100),
         cl::Optional);

namespace {
  
  struct BogusControlFlow : public FunctionPass {
    static char ID;
    bool flag;
    
    vector<function<void(Function &F, BasicBlock *basicBlock, vector<BasicBlock *> &pads)>> routeBox;
    
    BogusControlFlow() : FunctionPass(ID) {this->flag = true, initBox();}
    BogusControlFlow(bool flag) : FunctionPass(ID) {this->flag = flag, initBox();}
    
    void initBox() {
      routeBox = {
        
        /* slight1 */
        [](Function &F, BasicBlock *basicBlock, vector<BasicBlock *> &pads){
          BasicBlock::iterator ii = basicBlock->begin();
          if (basicBlock->getFirstNonPHIOrDbgOrLifetime())
            ii = (BasicBlock::iterator)basicBlock->getFirstNonPHIOrDbgOrLifetime();
          
          BasicBlock *original = basicBlock->splitBasicBlock(ii, "original");
          basicBlock->getTerminator()->eraseFromParent();
          
          int ibase = (int)llvm::cryptoutils->get_range(INT16_MAX);
          int iadd = (int)llvm::cryptoutils->get_range(INT8_MAX);
          
          Value *var1 = ConstantInt::get(Type::getInt32Ty(F.getContext()), ibase, false);
          Value *var2 = ConstantInt::get(Type::getInt32Ty(F.getContext()), ibase+iadd+1, false);
          
          ICmpInst * condition = new ICmpInst(*basicBlock, ICmpInst::ICMP_EQ, var1, var2);
          BranchInst::Create(basicBlock, original, (Value*)condition, basicBlock)->setBogusBranch(true);
        },
        
        /* slight2 */
        [](Function &F, BasicBlock *basicBlock, vector<BasicBlock *> &pads){
          BasicBlock::iterator ii = basicBlock->begin();
          if (basicBlock->getFirstNonPHIOrDbgOrLifetime())
            ii = (BasicBlock::iterator)basicBlock->getFirstNonPHIOrDbgOrLifetime();
          
          BasicBlock *original = basicBlock->splitBasicBlock(ii, "original");
          basicBlock->getTerminator()->eraseFromParent();
          
          BasicBlock *puzzleJmp = BasicBlock::Create(F.getContext(), "puzzleJmp", &F);
          new UnreachableInst(F.getContext(), puzzleJmp);
          
          int ibase = (int)llvm::cryptoutils->get_range(INT16_MAX);
          int iadd = (int)llvm::cryptoutils->get_range(INT8_MAX);
          
          Value *var1 = ConstantInt::get(Type::getInt32Ty(F.getContext()), ibase, false);
          Value *var2 = ConstantInt::get(Type::getInt32Ty(F.getContext()), ibase+iadd+1, false);
          
          ICmpInst * condition = new ICmpInst(*basicBlock, ICmpInst::ICMP_EQ, var1, var2);
          BranchInst::Create(puzzleJmp, original, (Value*)condition, basicBlock)->setBogusBranch(true);;
        },
        
        /* ultimate1 */
        /*
         [](Function &F, BasicBlock *basicBlock, vector<BasicBlock *> &pads){
         BasicBlock::iterator ii = basicBlock->begin();
         if (basicBlock->getFirstNonPHIOrDbgOrLifetime())
         ii = (BasicBlock::iterator)basicBlock->getFirstNonPHIOrDbgOrLifetime();
         
         BasicBlock *original = basicBlock->splitBasicBlock(ii, "original");
         basicBlock->getTerminator()->eraseFromParent();
         
         int select = llvm::cryptoutils->get_range(INT8_MAX) % pads.size();
         BasicBlock *puzzleJmp = pads.at(select);
         
         int ibase = (int)llvm::cryptoutils->get_range(INT16_MAX);
         int iadd = (int)llvm::cryptoutils->get_range(INT8_MAX);
         
         Value *var1 = ConstantInt::get(Type::getInt32Ty(F.getContext()), ibase, false);
         Value *var2 = ConstantInt::get(Type::getInt32Ty(F.getContext()), ibase+iadd, false);
         
         ICmpInst *condition = new ICmpInst(*basicBlock, ICmpInst::ICMP_EQ, var1, var2);
         BranchInst::Create(puzzleJmp, original, (Value*)condition, basicBlock)->setBogusBranch(true);
         }
         */
      };
    }
    
    bool checkParams() {
      if (!((bcf_rate > 0) && (bcf_rate <= 100))) {
        return false;
      }
      return true;
    }
    
    bool isInvoke(Function &F) {
      for (Function::iterator i = F.begin(); i != F.end(); ++i) {
        BasicBlock *bb = &*i;
        if (isa<InvokeInst>(bb->getTerminator())) {
          return true;
        }
      }
      return false;
    }
    
    bool optimize(Function &F) {
      errs() << "Running BCF On " << F.getName() << "\n";
      bogus(F);
      return true;
    }
    
    bool runOnFunction(Function &F) override {
      rp::Value config = Morphling::getConfig("obfuscation.bcfobf");
      if (config.HasMember("bcf_rate"))
        bcf_rate = config.FindMember("bcf_rate")->value.GetInt();
      
      if (!checkParams())
        return false;
      
      if (isInvoke(F))
       return false;
      
      if (Morphling::toObfuscate(flag, &F, "bcf")) {
        return optimize(F);
      }
      return false;
    }
    
    bool containsPHI(BasicBlock *b) {
      for (BasicBlock::iterator I = b->begin(), IE = b->end(); I != IE; ++I)
        if (isa<PHINode>(I))
          return true;
      return false;
    }
    
    bool canOptimized(BasicBlock* basicBlock){
      BasicBlock::iterator ii = basicBlock->begin();
      if (basicBlock->getFirstNonPHIOrDbgOrLifetime())
        ii = (BasicBlock::iterator)basicBlock->getFirstNonPHIOrDbgOrLifetime();
      if (ii == basicBlock->end())
        return false;
      if (!basicBlock->getTerminator())
        return false;
      return true;
    }
    
    bool bogus(Function &F) {
      bool optimized = false;
      
      std::vector<BasicBlock *> basicBlocks;
      Function::iterator i = F.begin();
      for (i++; i != F.end(); ++i) {
        BasicBlock *BB = &*i;
        if (!BB->isEHPad() && !BB->isLandingPad() && !containsPHI(BB))
          basicBlocks.push_back(BB);
      }
      
      std::vector<BasicBlock *> pads = basicBlocks;
      
      while (!basicBlocks.empty()) {
        BasicBlock *basicBlock = basicBlocks.back();
        basicBlocks.pop_back();
        
        if (!canOptimized(basicBlock))
          continue;
        
        if ((llvm::cryptoutils->get_range(INT16_MAX) % 100L) >= bcf_rate)
          continue;
        
        optimized = true;
        routeBox.at(llvm::cryptoutils->get_range(INT16_MAX) % routeBox.size())(F, basicBlock, pads);
      }
      
      return optimized;
    }
  };
}

char BogusControlFlow::ID = 0;
INITIALIZE_PASS(BogusControlFlow, "bcfobf", "Enable BogusControlFlow.", true, true)
FunctionPass *llvm::createBogusControlFlowPass() {return new BogusControlFlow();}
FunctionPass *llvm::createBogusControlFlowPass(bool flag) {return new BogusControlFlow(flag);}

