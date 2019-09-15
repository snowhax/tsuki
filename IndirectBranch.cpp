/*
 *  LLVM  Pass
 *  Note we only aim to support Darwin ObjC. GNUStep and other implementations
 *  are not considered
 Copyright (C) 2017 Zhang(https://github.com/Naville/)

 This program is free software: you can redistribute it and/or modify
 it under the terms of the GNU Affero General Public License as published
 by the Free Software Foundation, either version 3 of the License, or
 any later version.

 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU Affero General Public License for more details.

 You should have received a copy of the GNU Affero General Public License
 along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Obfuscation/Morphling.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

using namespace llvm;
using namespace std;

static cl::opt<int>
inb_rate("mh_inb_rate",
         cl::desc("don't tell you"),
         cl::value_desc("don't tell you"), cl::init(100),
         cl::Optional);


namespace llvm {
  struct IndirectBranch : public FunctionPass {
    static char ID;
    bool flag;

    IndirectBranch() : FunctionPass(ID) {
      this->flag = true;
    }
    IndirectBranch(bool flag) : FunctionPass(ID) {
      this->flag = flag;
    }

    StringRef getPassName() const override {
      return StringRef("IndirectBranch");
    }

    bool transform(Function &func, vector<BranchInst *> & bis) {
      if (0 == bis.size())
        return false;

      LLVMContext & ctx = func.getParent()->getContext();
      const DataLayout layout = func.getParent()->getDataLayout();
      IntegerType* ity = Type::getIntNTy(ctx, layout.getPointerSizeInBits());
      Value *zero = ConstantInt::get(ity, 0);

      for (BranchInst *bi : bis) {
        IRBuilder<> irb(bi);
        vector<BasicBlock *> bbs;

        if ((llvm::cryptoutils->get_range(INT16_MAX) % 100L) >= inb_rate)
          continue;
        
        /* [successor(1):false(0), successor(0):true(1)] */
        if (bi->getNumSuccessors() != 2)
          continue;
        
        bbs.push_back(bi->getSuccessor(1));
        bbs.push_back(bi->getSuccessor(0));

        /* confuse block address */
        vector<Constant *> blockAddresses;
        for (unsigned i = 0; i < bbs.size(); i++) {
          blockAddresses.push_back(BlockAddress::get(bbs[i]));
        }

        /* create table */
        ArrayType *ayt = ArrayType::get(Type::getInt8PtrTy(ctx), bbs.size());
        Constant *blockAddressArray = ConstantArray::get(ayt, ArrayRef<Constant *>(blockAddresses));
        GlobalVariable *table = new GlobalVariable(*func.getParent(), ayt, false,
                                                   GlobalValue::LinkageTypes::PrivateLinkage,
                                                   blockAddressArray, "IndirectBranchingTable");

        /* create brinst */
        appendToCompilerUsed(*func.getParent(), {table});
        Value *index = irb.CreateZExt(bi->getCondition(), ity);
        Value *gep = irb.CreateGEP(table, {zero, index});
        LoadInst *li = irb.CreateLoad(gep, "IndirectBranchingTargetAddress");
        IndirectBrInst *indirBr = IndirectBrInst::Create(li, bbs.size());
        indirBr->addDestination(bbs[0]);
        indirBr->addDestination(bbs[1]);

        /* apply */
        ReplaceInstWithInst(bi, indirBr);
      }
      return true;
    }

    bool runOnFunction(Function &func) override {
      if (!Morphling::toObfuscate(flag, &func, "indibr"))
        return false;

      rp::Value config = Morphling::getConfig("obfuscation.inbobf");
      if (config.HasMember("inb_rate"))
        inb_rate = config.FindMember("inb_rate")->value.GetInt();
      
      errs() << "Running IndirectBranch On " << func.getName() << "\n";

      vector<BranchInst *> bis;
      for (inst_iterator i = inst_begin(func); i != inst_end(func); i++) {
        BranchInst *bi = dyn_cast<BranchInst>(&(*i));
        if (bi && bi->isConditional() && !bi->isBogusBranch())
          bis.push_back(bi);
      }
      return transform(func, bis);
    }
  };
}

char IndirectBranch::ID = 0;
INITIALIZE_PASS(IndirectBranch, "indibran", "IndirectBranching", true, true)
FunctionPass *llvm::createIndirectBranchPass() { return new IndirectBranch();}
FunctionPass *llvm::createIndirectBranchPass(bool flag) {return new IndirectBranch(flag);}
