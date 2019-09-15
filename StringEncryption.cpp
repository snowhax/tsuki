
#include <cstdlib>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Obfuscation/CryptoUtils.h"
#include "llvm/Transforms/Obfuscation/Morphling.h"
#include "llvm/Transforms/Obfuscation/StringEncryption.h"


using namespace llvm;
using namespace std;

#define DEBUG_TYPE "StringEncryption"

static cl::opt<int>
lower("strcry_lower",
      cl::desc(""),
      cl::value_desc("strcry_lower"), cl::init(60),
      cl::Optional);

static cl::opt<int>
upper("strcry_upper",
      cl::desc(""),
      cl::value_desc("strcry_upper"), cl::init(90),
      cl::Optional);


StringEncryption::StringEncryption() : ModulePass(ID), decoder(NULL) {
  this->flag = true;
  initBox();
}

StringEncryption::StringEncryption(bool flag) : ModulePass(ID), decoder(NULL) {
  this->flag = flag;
  initBox();
}

StringRef StringEncryption::getPassName() const {
  return StringRef("StringEncryption");
}

void StringEncryption::initBox() {
  encBox = {
    /* box 0  */
    [](StringEncryption* pass,
       StringRef snippet,
       uint8_t& seed) {
      char* buf = const_cast<char*>(snippet.data());
      unsigned size = snippet.size();
      uint8_t last = seed;
      for (unsigned i = 0; i != size; ++i) {
        seed ^= buf[i];
        buf[i] = last;
        last = seed;
      }
    },
    /* box 1 */
    [](StringEncryption* pass,
       StringRef snippet,
       uint8_t& seed){
      char* buf = const_cast<char*>(snippet.data());
      unsigned size = snippet.size();
      for (unsigned i = 0; i != size; ++i) {
        buf[i] += 1;
      }
    },
    /* box 2 */
    [](StringEncryption* pass,
       StringRef snippet,
       uint8_t& seed){
      char* buf = const_cast<char*>(snippet.data());
      unsigned size = snippet.size();
      for (unsigned i = 0; i != size; ++i) {
        buf[i] -= 1;
        seed -= 1;  /* confuse seed */
      }
    }
  };
  
  decBox = {
    /* box 0  */
    [](StringEncryption* pass,
       IRBuilder<>& builder,
       Value* pstr, PHINode* i, Value* pseed,
       BasicBlock* exit){
      /* xor */
      Value *index = i;
      Value *getchar = builder.CreateGEP(pstr, ArrayRef<Value*>(&index, 1));
      LoadInst *ori = builder.CreateLoad(getchar, false, "ori");
      Value *res = builder.CreateXor(ori, builder.CreateLoad(pseed), "res");
      builder.CreateStore(ori, pseed, false);
      builder.CreateStore(res, getchar, false);
      
      /* update i */
      Value *subi = builder.CreateSub(i, ConstantInt::get(pass->ity, 1));
      Value *cmpi = builder.CreateICmpSGE(subi, ConstantInt::get(pass->ity, 0));
      BasicBlock* block = builder.GetInsertBlock();
      builder.CreateCondBr(cmpi, block, exit);
      i->addIncoming(subi, block);
    },
    /* box 1  */
    [](StringEncryption* pass,
       IRBuilder<>& builder,
       Value* pstr, PHINode* i, Value* pseed,
       BasicBlock* exit){
      /* sub */
      Value *index = i;
      Value *getchar = builder.CreateGEP(pstr, ArrayRef<Value*>(&index, 1));
      LoadInst *ori = builder.CreateLoad(getchar, false, "ori");
      Value *res = builder.CreateSub(ori, ConstantInt::get(pass->i8ty, 1));
      builder.CreateStore(res, getchar, false);
      
      /* update i */
      Value *subi = builder.CreateSub(i, ConstantInt::get(pass->ity, 1));
      Value *cmpi = builder.CreateICmpSGE(subi, ConstantInt::get(pass->ity, 0));
      BasicBlock* block = builder.GetInsertBlock();
      builder.CreateCondBr(cmpi, block, exit);
      i->addIncoming(subi, block);
    },
    /* box 2  */
    [](StringEncryption* pass,
       IRBuilder<>& builder,
       Value* pstr, PHINode* i, Value* pseed,
       BasicBlock* exit){
      /* add */
      Value *index = i;
      Value *getchar = builder.CreateGEP(pstr, ArrayRef<Value*>(&index, 1));
      LoadInst *ori = builder.CreateLoad(getchar, false, "ori");
      Value *res = builder.CreateAdd(ori, ConstantInt::get(pass->i8ty, 1));
      Value *seed = builder.CreateLoad(pseed);
      seed = builder.CreateAdd(seed, ConstantInt::get(pass->i8ty, 1));
      builder.CreateStore(res, getchar, false);
      builder.CreateStore(seed, pseed, false);
      
      /* update i */
      Value *subi = builder.CreateSub(i, ConstantInt::get(pass->ity, 1));
      Value *cmpi = builder.CreateICmpSGE(subi, ConstantInt::get(pass->ity, 0));
      BasicBlock* block = builder.GetInsertBlock();
      builder.CreateCondBr(cmpi, block, exit);
      i->addIncoming(subi, block);
    }
  };
}

void StringEncryption::initializeType(Module &M) {
  LLVMContext & ctx = M.getContext();
  const DataLayout layout = M.getDataLayout();
  bitSize = layout.getPointerSizeInBits();
  i8ty = Type::getInt8Ty(ctx);
  i8pty = Type::getInt8PtrTy(ctx);
  ity = Type::getIntNTy(ctx, bitSize);
}

bool StringEncryption::runOnModule(Module &M) {
  if (!flag) return false;
  
  rp::Value config = Morphling::getConfig("obfuscation.strcry");

  if (config.HasMember("lower"))
    lower = config.FindMember("lower")->value.GetInt();
  
  if (config.HasMember("upper"))
  upper = config.FindMember("upper")->value.GetInt();
  
  bool changed = false;
  initializeType(M);
  
  vector<GlobalVariable *> gvs;
  unsigned count = collectString(M, gvs);
  errs() << "collect string count:" << count << "\n";
  
  Constant* table = transform(M, gvs, seed);
  if (table) {
    decoder = createDecoder(M, (ConstantArray*)table, seed);
    changed = true;
  }
  return changed;
}

unsigned StringEncryption::collectString(Module &M, vector<GlobalVariable *> &gvs) {
  /* find constant string */
  for (Module::global_iterator gi = M.global_begin(); gi != M.global_end(); ++gi) {
    GlobalVariable* gv = &(*gi);
    std::string section(gv->getSection());
    std::string name = gv->getName().str();
    
    /* filter */
    if (name.substr(0,4) != ".str") continue;
    if (section == "llvm.metadata") continue;
    if (!gv->isConstant()) continue;
    if (!gv->hasInitializer()) continue;
    
    Constant *init = gv->getInitializer();
    ConstantDataSequential *cdata = dyn_cast<ConstantDataSequential>(init);
    
    if (!cdata) continue;
    if (!cdata->getElementType()->isIntegerTy()) continue;
    
    gvs.push_back(gv);
  }
  
  return gvs.size();
}

static __inline__ __attribute__((always_inline))
Fixup MakeFixup(GlobalVariable *gv, int type, unsigned offset, unsigned size) {
  Fixup fix;
  fix.gv = gv;
  fix.type = type;
  fix.offset = offset;
  fix.size = size;
  return fix;
}

Constant *StringEncryption::transform(Module &M, vector<GlobalVariable *> &gvs, uint8_t &seed) {
  vector<Fixup> fixups;
  seed = llvm::cryptoutils->get_range(UINT8_MAX);
  
  for (GlobalVariable *gv : gvs) {
    Constant *init = gv->getInitializer();
    ConstantDataSequential *cdata = dyn_cast<ConstantDataSequential>(init);
    unsigned per = cdata->getElementByteSize();
    
    /* filter empty string */
    unsigned count = cdata->getNumElements();
    if (count <= 1) continue;
    
    /* create copy */
    StringRef ori = cdata->getRawDataValues();
    unsigned osize = per * count;
    vector<char> buf(ori.begin(), ori.end());
    
    /* calculating range */
    /* [lower,upper] */
    float percent = (lower + (cryptoutils->get_range(INT16_MAX) % (upper-lower+1))) / 100.f;
    
    unsigned esize = floor(osize * percent);
    if (esize == 0) continue;
    
    unsigned offset = osize - esize;
    if (offset != 0)
      offset = cryptoutils->get_range(INT32_MAX) % offset;
    
    int index = cryptoutils->get_range(INT16_MAX) % encBox.size();
    encBox.at(index)(this, StringRef(buf.data() + offset, esize), seed);
    
    /* replace and fix string writable */
    Type* ty = cdata->getType();
    Constant* replace = ConstantDataArray::getImpl(StringRef(buf.data(), buf.size()), ty);
    gv->setConstant(false);
    gv->setInitializer(replace);
    gv->setSection("");
    
    fixups.push_back(MakeFixup(gv, index, offset, esize));
  }
  
  /* nothing to be done */
  if (0 == fixups.size())
    return NULL;
  
  return createTable(M, fixups, seed);
}

Constant* StringEncryption::createTable(Module &M, std::vector<Fixup> &fixups, uint8_t seed) {
  vector<Type *> types;
  types.push_back(i8pty);
  types.push_back(ity);
  StructType* fixty = StructType::create(ArrayRef<Type *>(types), "fixty");
  
  /* create table */
  vector<Constant *> items;
  for (unsigned i = 0; i < fixups.size(); i++) {
    Fixup fix = fixups[i];
    Constant* gv = ConstantExpr::getPtrToInt(fix.gv, ity);
    Constant* offset = ConstantInt::get(ity, fix.offset);
    Constant* ngv = ConstantExpr::getAdd(gv, offset);
    ngv = ConstantExpr::getIntToPtr(ngv, i8pty);
    Constant* info = ConstantInt::get(ity, (fix.type << (bitSize - 4)) | fix.size);
    vector<Constant *> cs = {ngv, info};
    Constant* item = ConstantStruct::get(fixty, ArrayRef<Constant *>(cs));
    items.push_back(item);
  }
  
  ArrayType *ayt = ArrayType::get(fixty, items.size());
  return ConstantArray::get(ayt, ArrayRef<Constant *>(items));
}

static llvm::Function *GetPrintfDeclaration(llvm::Module &M) {
  llvm::Type* argsT[] = {llvm::Type::getInt8PtrTy(M.getContext())};
  llvm::Type* ity = llvm::Type::getInt32Ty(M.getContext());
  llvm::FunctionType* funcT = FunctionType::get(ity, argsT, true);
  if (auto* F = M.getFunction("printf")) {
    return F;
  }
  return llvm::Function::Create(funcT, llvm::GlobalVariable::ExternalLinkage, "printf", &M);
}

Function* StringEncryption::createDecoder(Module &M, ConstantArray* array, uint8_t seed) {
  LLVMContext & ctx = M.getContext();
  FunctionType* fty = FunctionType::get(Type::getVoidTy(ctx), {}, false);
  GlobalValue::LinkageTypes lktype = GlobalValue::LinkageTypes::PrivateLinkage;
  
  GlobalVariable *table = new GlobalVariable(M, array->getType(), true, lktype, array);
  
  Function* fun = Function::Create(fty, lktype, "", &M);
  fun->setCallingConv(CallingConv::C);
  
  /* constant */
  Value *zero = ConstantInt::get(ity, 0);
  Value *one = ConstantInt::get(ity, 1);
  Value *mask = ConstantInt::get(ity, ~(0xfull << (bitSize-4)));
  
  /* create block */
  BasicBlock* entry = BasicBlock::Create(ctx, "entry", fun);
  BasicBlock* leave = BasicBlock::Create(ctx, "leave", fun);
  BasicBlock* forJbody = BasicBlock::Create(ctx, "forJbody", fun);
  BasicBlock* forJend = BasicBlock::Create(ctx, "forJend", fun);
  BasicBlock* dispatcher = BasicBlock::Create(ctx, "dispatcher", fun);
  
  IRBuilder<> builder(entry);
  
  /* printf decode
  llvm::Function* printf = GetPrintfDeclaration(M);;
  Value *args[2] = {
    Morphling::getCString(M, "morphling total decode:%d\n"),
    ConstantInt::get(ity, array->getType()->getNumElements()),
  };
  builder.CreateCall(printf,  ArrayRef<Value*>(args, 2));
   */

  /* init local variable */
  AllocaInst* pseed = builder.CreateAlloca(i8ty, 0, "pseed");
  builder.CreateStore(builder.getInt8(seed), pseed);
  
  /* goto begin */
  builder.CreateBr(forJbody);
  /* init j(phi) */
  builder.SetInsertPoint(forJbody);
  PHINode *j = builder.CreatePHI(ity, 2, "j");
  Value *jbegin = ConstantInt::get(ity, array->getType()->getNumElements() - 1);
  j->addIncoming(jbegin, entry);
  
  /* update local variable */
  Value *strIndex[3] = {builder.getInt32(0), j, builder.getInt32(0)};
  Value *getpstr = builder.CreateGEP(table, ArrayRef<Value*>(strIndex, 3));
  LoadInst *pstr = builder.CreateLoad(getpstr);
  Value *infoIndex[3] = {builder.getInt32(0), j, builder.getInt32(1)};
  Value *getpinfo = builder.CreateGEP(table, ArrayRef<Value*>(infoIndex, 3));
  Value *info = builder.CreateLoad(getpinfo, "info");
  /* goto switch */
  builder.CreateBr(dispatcher);
  
  /* restore */
  builder.SetInsertPoint(dispatcher);
  Value *size = builder.CreateAnd(info, mask);
  size = builder.CreateSub(size, one);
  Value *type = builder.CreateLShr(info, bitSize-4);
  SwitchInst* sw = builder.CreateSwitch(type, forJend);
  
  for (unsigned idx = 0; idx < decBox.size(); idx++) {
    BasicBlock* block = BasicBlock::Create(ctx, "", fun);
    builder.SetInsertPoint(block);
    /* init i(phi) */
    PHINode *i = builder.CreatePHI(ity, 2, "i");
    i->addIncoming(size, dispatcher);
    decBox.at(idx)(this, builder, pstr, i, pseed, forJend);
    sw->addCase(ConstantInt::get(ity, idx), block);
  }
  
  /* update j */
  builder.SetInsertPoint(forJend);
  Value *subj = builder.CreateSub(j, one);
  j->addIncoming(subj, forJend);
  Value *cmpj = builder.CreateICmpSGE(subj, zero);
  builder.CreateCondBr(cmpj, forJbody, leave);
  
  builder.SetInsertPoint(leave);
  builder.CreateRetVoid();
  
  //fun->viewCFG();
  
  return fun;
}

ModulePass *llvm::createStringEncryptionPass() { return new StringEncryption(); }
ModulePass *llvm::createStringEncryptionPass(bool flag) {
  return new StringEncryption(flag);
}


char StringEncryption::ID = 0;
INITIALIZE_PASS(StringEncryption, "strcry", "Enable String Encryption", true, true)
