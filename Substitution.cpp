
#include "llvm/Transforms/Obfuscation/Substitution.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Transforms/Obfuscation/Morphling.h"

#define DEBUG_TYPE "substitution"

using namespace std;
using namespace llvm;

static cl::opt<int>
sub_time("sub_loop",
         cl::desc("this don't tell you"),
         cl::value_desc("this don't tell you"), cl::init(1), cl::Optional);

static cl::opt<unsigned int>
sub_rate("sub_prob",
            cl::desc("this don't tell you"),
            cl::value_desc("this don't tell you"), cl::init(50), cl::Optional);


namespace {

  struct Substitution : public FunctionPass {
    static char ID;
    bool flag;

    vector<function<void(BinaryOperator *bo)>> addBox;
    vector<function<void(BinaryOperator *bo)>> subBox;
    vector<function<void(BinaryOperator *bo)>> andBox;
    vector<function<void(BinaryOperator *bo)>>  orBox;
    vector<function<void(BinaryOperator *bo)>> xorBox;

    Substitution() : FunctionPass(ID) {this->flag = true, initBox();}
    Substitution(bool flag) : Substitution() {this->flag = flag, initBox();}

    void initBox() {
      addBox = {
        /* a + b = a - (-b) */
        [](BinaryOperator *bo){
          assert(bo->getOpcode() == Instruction::Add);
          BinaryOperator *op = NULL;
          op = BinaryOperator::CreateNeg(bo->getOperand(1), "", bo);
          op = BinaryOperator::Create(Instruction::Sub, bo->getOperand(0), op, "", bo);
          bo->replaceAllUsesWith(op);
        },
        /* a + b = -(-a + (-b)) */
        [](BinaryOperator *bo){
          assert(bo->getOpcode() == Instruction::Add);
          BinaryOperator *op, *op2 = NULL;
          op = BinaryOperator::CreateNeg(bo->getOperand(0), "", bo);
          op2 = BinaryOperator::CreateNeg(bo->getOperand(1), "", bo);
          op = BinaryOperator::Create(Instruction::Add, op, op2, "", bo);
          op = BinaryOperator::CreateNeg(op, "", bo);
          bo->replaceAllUsesWith(op);
        },
        /* a + b = a - r + b + r */
        [](BinaryOperator *bo){
          assert(bo->getOpcode() == Instruction::Add);
          BinaryOperator *op = NULL;
          Type *ty = bo->getType();
          ConstantInt *co = (ConstantInt*)ConstantInt::get(ty, llvm::cryptoutils->get_range(INT32_MAX));
          op = BinaryOperator::Create(Instruction::Sub, bo->getOperand(0), co, "", bo);
          op = BinaryOperator::Create(Instruction::Add, op, bo->getOperand(1), "", bo);
          op = BinaryOperator::Create(Instruction::Add, op, co, "", bo);
          bo->replaceAllUsesWith(op);
        },
      };

      subBox = {
        /* a - b = a + (-b) */
        [](BinaryOperator *bo){
          assert(bo->getOpcode() == Instruction::Sub);
          BinaryOperator *op = NULL;
          op = BinaryOperator::CreateNeg(bo->getOperand(1), "", bo);
          op = BinaryOperator::Create(Instruction::Add, bo->getOperand(0), op, "", bo);
          bo->replaceAllUsesWith(op);
        },
        /* a - b = -(b - a) */
        [](BinaryOperator *bo){
          assert(bo->getOpcode() == Instruction::Sub);
          BinaryOperator *op = NULL;
          op = BinaryOperator::Create(Instruction::Sub, bo->getOperand(1), bo->getOperand(0), "", bo);
          op = BinaryOperator::CreateNeg(op, "", bo);
          bo->replaceAllUsesWith(op);
        },
      };

      andBox = {
        /* a & b = b & a */
        [](BinaryOperator *bo){
          assert(bo->getOpcode() == Instruction::And);
          BinaryOperator *op = NULL;
          op = BinaryOperator::Create(Instruction::And, bo->getOperand(1), bo->getOperand(0), "", bo);
          bo->replaceAllUsesWith(op);
        },
        /* a & b == (a^~b) & a */
        [](BinaryOperator *bo){
          assert(bo->getOpcode() == Instruction::And);
          BinaryOperator *op, *op2 = NULL;
          op = BinaryOperator::CreateNot(bo->getOperand(1), "", bo);
          op2 = BinaryOperator::Create(Instruction::Xor, bo->getOperand(0), op, "", bo);
          op = BinaryOperator::Create(Instruction::And, op2, bo->getOperand(0), "", bo);
          bo->replaceAllUsesWith(op);
        },
      };

      orBox = {
        /* a | b = b | a */
        [](BinaryOperator *bo){
          assert(bo->getOpcode() == Instruction::Or);
          BinaryOperator *op = NULL;
          op = BinaryOperator::Create(Instruction::Or, bo->getOperand(1), bo->getOperand(0), "", bo);
          bo->replaceAllUsesWith(op);
        },
        /* a | b = (a & b) | (a ^ b) */
        [](BinaryOperator *bo){
          assert(bo->getOpcode() == Instruction::Or);
          BinaryOperator *op, *op1 = NULL;
          op = BinaryOperator::Create(Instruction::And, bo->getOperand(0), bo->getOperand(1), "", bo);
          op1 = BinaryOperator::Create(Instruction::Xor, bo->getOperand(0), bo->getOperand(1), "", bo);
          op = BinaryOperator::Create(Instruction::Or, op, op1, "", bo);
          bo->replaceAllUsesWith(op);
        },
      };

      xorBox = {
        /* a ^ b = b ^ a */
        [](BinaryOperator *bo){
          assert(bo->getOpcode() == Instruction::Xor);
          BinaryOperator *op = NULL;
          op = BinaryOperator::Create(Instruction::Xor, bo->getOperand(1), bo->getOperand(0), "", bo);
          bo->replaceAllUsesWith(op);
        },
        /* a ~ b => a = (!a && b) | (a && !b) */
        [](BinaryOperator *bo){
          assert(bo->getOpcode() == Instruction::Xor);
          BinaryOperator *op,*op1 = NULL;
          op = BinaryOperator::CreateNot(bo->getOperand(0), "", bo);
          op = BinaryOperator::Create(Instruction::And, bo->getOperand(1), op, "", bo);
          op1 = BinaryOperator::CreateNot(bo->getOperand(1), "", bo);
          op1 = BinaryOperator::Create(Instruction::And, bo->getOperand(0), op1, "", bo);
          op = BinaryOperator::Create(Instruction::Or, op, op1, "", bo);
          bo->replaceAllUsesWith(op);
        },
      };
    }

    bool checkParams() {
      if (sub_time <= 0) {
        errs() << "-sub_loop=x must be x > 0";
        return false;
      }
      if (sub_rate > 100) {
        errs() << "-sub_prob=x must be 0 < x <= 100";
        return false;
      }
      return true;
    }

    bool runOnFunction(Function &F) {
      if (!checkParams())
        return false;

      if (Morphling::toObfuscate(flag, &F, "sub")) {
        substitute(F);
        return true;
      }
      return false;
    }

    bool resolve(Instruction *inst) {
      BinaryOperator* bo = cast<BinaryOperator>(inst);
      switch (inst->getOpcode()) {
        case BinaryOperator::Add:
          addBox.at(llvm::cryptoutils->get_range(INT16_MAX) % addBox.size())(bo);
          break;
        case BinaryOperator::Sub:
          subBox.at(llvm::cryptoutils->get_range(INT16_MAX) % subBox.size())(bo);
          break;
        case Instruction::And:
          andBox.at(llvm::cryptoutils->get_range(INT16_MAX) % andBox.size())(bo);
          break;
        case Instruction::Or:
          orBox.at(llvm::cryptoutils->get_range(INT16_MAX) % orBox.size())(bo);
          break;
        case Instruction::Xor:
          xorBox.at(llvm::cryptoutils->get_range(INT16_MAX) % xorBox.size())(bo);
          break;
        default:
          return false;
      }
      return true;
    }

    bool shouldSubstitute(Instruction & inst) {
      return inst.isBinaryOp() && (cryptoutils->get_range(100) <= sub_rate);
    }

    bool substitute(Function &f) {
      int n = sub_time;
      while (n--) {
        for (Function::iterator bb = f.begin(); bb != f.end(); ++bb)
          for (BasicBlock::iterator inst = bb->begin(); inst != bb->end(); ++inst)
            if (shouldSubstitute(*inst))
              resolve(&*inst);
      }
      return false;
    }
  };
}

char Substitution::ID = 0;
INITIALIZE_PASS(Substitution, "subobf", "Enable Instruction Substitution.", true, true)
FunctionPass *llvm::createSubstitutionPass() { return new Substitution(); }
FunctionPass *llvm::createSubstitutionPass(bool flag) {return new Substitution(flag);}
