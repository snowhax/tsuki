//===- GlobalOpt.cpp - Optimize Global Variables --------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass transforms simple global variables that never have their address
// taken.  If obviously true, it marks read/write globals as constant, deletes
// variables only stored to, etc.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/IPO.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Constants.h"
#include "llvm/Pass.h"
#include "llvm/ADT/Triple.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/CtorUtils.h"
#include "llvm/Transforms/Utils/GlobalStatus.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Obfuscation/Morphling.h"

using namespace llvm;
using namespace std;

#define DEBUG_TYPE "LTOMorphling"

namespace llvm {
  
  enum NonFragileClassFlags {
    /// Is a meta-class.
    NonFragileABI_Class_Meta = 0x00001,
    /// Is a root class.
    NonFragileABI_Class_Root = 0x00002,
    /// Has a C++ constructor and destructor.
    NonFragileABI_Class_HasCXXStructors = 0x00004,
    /// Has hidden visibility.
    NonFragileABI_Class_Hidden = 0x00010,
    /// Has the exception attribute.
    NonFragileABI_Class_Exception = 0x00020,
    /// (Obsolete) ARC-specific: this class has a .release_ivars method
    NonFragileABI_Class_HasIvarReleaser = 0x00040,
    /// Class implementation was compiled under ARC.
    NonFragileABI_Class_CompiledByARC = 0x00080,
    /// Class has non-trivial destructors, but zero-initialization is okay.
    NonFragileABI_Class_HasCXXDestructorOnly = 0x00100
  };
  
  struct LTOMorphling : public ModulePass {
    
    static char ID;
    bool flag;
    
    StringRef getPassName() const override { return StringRef("LTOMorphling"); }
    LTOMorphling() : ModulePass(ID) {this->flag = true;}
    LTOMorphling(bool flag) : ModulePass(ID) {this->flag = flag;}
    
  public:
    
    bool runOnModule(Module &M) override {
      bool changed = false;
      if (!Morphling::centerIsAlive())
        M.getContext().diagnose(MorphlingDiagnosticInfo("morphling is not alive!"));
      
      rp::Value sortobf = Morphling::getConfig("obfuscation.sortobf");
      if (sortobf.HasMember("symbol") &&
          sortobf.FindMember("symbol")->value.GetBool())
        Morphling::solveSymbol(M);
      
      rp::Value config = Morphling::getConfig("obfuscation.strcry");
      if (!ObjCNonFragileABITypesHelper(M))
        return changed;
      
      if (!config.IsNull()) {
        StringEncryption* MP = (StringEncryption*)createStringEncryptionPass(true);
        MP->runOnModule(M);
        if (MP->decoder) {
          GlobalVariable * TClass = createMorphling("Morphling", MP->decoder);
          addClassList(TClass, "OBJC_LABEL_NONLAZY_CLASS_$", "__DATA, __objc_nlclslist, regular, no_dead_strip");
          changed = true;
        }
        delete MP;
      }
      return changed;
    }
    
  private:
    unsigned ObjCABI;
    
    GlobalVariable *ObjCEmptyCacheVar;
    GlobalVariable *ObjCEmptyVtableVar;
    
    Type *Int32Ty;
    Type *PtrTy;
    Type *ObjectPtrTy;
    Type *SelectorPtrTy;
    StructType *ClassnfABITy;
    Type *ClassnfABIPtrTy;
    Type *CacheTy;
    Type *CachePtrTy;
    Type *ImpnfABITy;
    StructType *ClassRonfABITy;
    
    StructType *MethodTy;
    StructType *MethodListnfABITy;
    Type *MethodListnfABIPtrTy;
    
    StructType *ProtocolnfABITy;
    Type *ProtocolnfABIPtrTy;
    StructType *ProtocolListnfABITy;
    Type *ProtocolListnfABIPtrTy;
    
    StructType *IvarnfABITy;
    StructType *IvarListnfABITy;
    Type *IvarListnfABIPtrTy;
    
    StructType *PropertyTy;
    StructType *PropertyListTy;
    Type *PropertyListPtrTy;
    
    StringMap<GlobalVariable*> ClassNames;
    StringMap<GlobalVariable*> MethodVarNames;
    StringMap<GlobalVariable*> MethodVarTypes;
    
    Module *MD;
    
    GlobalVariable *CreateMetadataVar(Twine Name, Constant *Init, StringRef Section, unsigned Align) {
      Type *Ty = Init->getType();
      GlobalVariable *GV = new GlobalVariable(*MD, Ty, false,
                                              GlobalValue::PrivateLinkage,
                                              Init, Name);
      if (!Section.empty()) GV->setSection(Section);
      if (Align) GV->setAlignment(Align);
      return GV;
    }
    
    static
    Constant *getConstantGEP(LLVMContext &VMContext, Constant *C, unsigned idx0, unsigned idx1) {
      Value *Idxs[] = {
        ConstantInt::get(Type::getInt32Ty(VMContext), idx0),
        ConstantInt::get(Type::getInt32Ty(VMContext), idx1)
      };
      return ConstantExpr::getGetElementPtr(0, C, Idxs);
    }
    
    Constant *GetMethodVarType(StringRef TypeStr) {
      LLVMContext &VMContext = MD->getContext();
      GlobalVariable *&Entry = MethodVarTypes[TypeStr];
      if (!Entry) {
        Entry = CreateMetadataVar("OBJC_METH_VAR_TYPE_",
                                  ConstantDataArray::getString(VMContext, TypeStr),
                                  ((ObjCABI == 2) ? "__TEXT,__objc_methtype,cstring_literals"
                                   : "__TEXT,__cstring,cstring_literals"), 1);
      }
      return getConstantGEP(VMContext, Entry, 0, 0);
    }
    
    Constant *GetMethodVarName(StringRef Sel) {
      LLVMContext &VMContext = MD->getContext();
      GlobalVariable *&Entry = MethodVarNames[Sel];
      if (!Entry) {
        Entry = CreateMetadataVar("OBJC_METH_VAR_NAME_",
                                  ConstantDataArray::getString(VMContext, Sel),
                                  ((ObjCABI == 2) ? "__TEXT,__objc_methname,cstring_literals"
                                   : "__TEXT,__cstring,cstring_literals"), 1);
      }
      return getConstantGEP(VMContext, Entry, 0, 0);
    }
    
    Constant *GetMethodConstant(Function *Fn, StringRef Sel, StringRef TypeStr) {
      Constant *Method[] = {GetMethodVarName(Sel),
        GetMethodVarType(TypeStr),
        ConstantExpr::getBitCast(Fn, PtrTy)};
      return ConstantStruct::get(MethodTy, Method);
    }
    
    Constant *GetClassName(StringRef RuntimeName) {
      LLVMContext &VMContext = MD->getContext();
      GlobalVariable *&Entry = ClassNames[RuntimeName];
      if (!Entry) {
        Entry = CreateMetadataVar("OBJC_CLASS_NAME_",
                                  ConstantDataArray::getString(VMContext, RuntimeName),
                                  ((ObjCABI == 2) ? "__TEXT,__objc_classname,cstring_literals"
                                   : "__TEXT,__cstring,cstring_literals"), 1);
      }
      return getConstantGEP(VMContext, Entry, 0, 0);
    }
    
    Constant *EmitMethodList(Twine Name, const char *Section, ArrayRef<Constant*> Methods) {
      if (Methods.empty())
        return Constant::getNullValue(MethodListnfABIPtrTy);
      
      const DataLayout &DL = MD->getDataLayout();
      Constant *Values[3];
      unsigned Size = DL.getTypeAllocSize(MethodTy);
      Values[0] = ConstantInt::get(Int32Ty, Size);
      Values[1] = ConstantInt::get(Int32Ty, Methods.size());
      Values[2] = ConstantArray::get(ArrayType::get(MethodTy, Methods.size()), Methods);
      Constant *Init = ConstantStruct::getAnon(Values);
      GlobalVariable *GV = new GlobalVariable(*MD, Init->getType(), false,
                                              GlobalValue::PrivateLinkage,
                                              Init, Name);
      GV->setAlignment(DL.getABITypeAlignment(Init->getType()));
      GV->setSection(Section);
      return ConstantExpr::getBitCast(GV, MethodListnfABIPtrTy);
    }
    
    // struct _class_ro_t {
    //   uint32_t const flags;
    //   uint32_t const instanceStart;
    //   uint32_t const instanceSize;
    //   uint32_t const reserved;  // only when building for 64bit targets
    //   const uint8_t * const ivarLayout;
    //   const char *const name;
    //   const struct _method_list_t * const baseMethods;
    //   const struct _objc_protocol_list *const baseProtocols;
    //   const struct _ivar_list_t *const ivars;
    //   const uint8_t * const weakIvarLayout;
    //   const struct _prop_list_t * const properties;
    // }
    
    GlobalVariable * BuildClassRoTInitializer(unsigned flags, StringRef ClassName,
                                              std::vector<Constant*> &Methods) {
      Constant *Values[10]; // 11 for 64bit targets!
      const DataLayout &DL = MD->getDataLayout();
      
      bool isMeta = flags & NonFragileABI_Class_Meta;
      
      Type *InstanceType = isMeta ? ClassnfABITy : ObjectPtrTy;
      std::string MethodListName = isMeta ?
      std::string("\01l_OBJC_$_CLASS_METHODS_") + ClassName.str() :
      std::string("\01l_OBJC_$_INSTANCE_METHODS_") + ClassName.str();
      
      uint32_t InstanceStart = DL.getTypeAllocSize(InstanceType);
      uint32_t InstanceSize = InstanceStart;
      
      Values[0] = ConstantInt::get(Int32Ty, flags);
      Values[1] = ConstantInt::get(Int32Ty, InstanceStart);
      Values[2] = ConstantInt::get(Int32Ty, InstanceSize);
      Values[3] = Constant::getNullValue(PtrTy);
      Values[4] = GetClassName(ClassName);
      Values[5] = EmitMethodList(MethodListName, "__DATA, __objc_const", Methods);
      Values[6] = Constant::getNullValue(ProtocolListnfABIPtrTy);
      Values[7] = Constant::getNullValue(IvarListnfABIPtrTy);
      Values[8] = Constant::getNullValue(PtrTy);
      Values[9] = Constant::getNullValue(PropertyListPtrTy);
      
      Constant *Init = ConstantStruct::get(ClassRonfABITy, Values);
      GlobalVariable *CLASS_RO_GV = new GlobalVariable(*MD,
                                                       ClassRonfABITy,
                                                       false,
                                                       GlobalValue::PrivateLinkage,
                                                       Init,
                                                       isMeta ?
                                                       std::string("\01l_OBJC_METACLASS_RO_$_") + ClassName :
                                                       std::string("\01l_OBJC_CLASS_RO_$_") + ClassName);
      
      CLASS_RO_GV->setAlignment(DL.getABITypeAlignment(ClassRonfABITy));
      CLASS_RO_GV->setSection("__DATA, __objc_const");
      return CLASS_RO_GV;
    }
    
    GlobalVariable *BuildClassMetaData(const std::string &ClassName,
                                       Constant *IsAGV,
                                       Constant *SuperClassGV,
                                       Constant *ClassRoGV,
                                       bool HiddenVisibility, bool Weak) {
      Constant *Values[] = {
        IsAGV,
        SuperClassGV,
        ObjCEmptyCacheVar,  // &ObjCEmptyCacheVar
        ObjCEmptyVtableVar, // &ObjCEmptyVtableVar
        ClassRoGV           // &CLASS_RO_GV
      };
      if (!Values[1])
        Values[1] = Constant::getNullValue(ClassnfABIPtrTy);
      if (!Values[3])
        Values[3] = Constant::getNullValue(PointerType::getUnqual(ImpnfABITy));
      
      Constant *Init = ConstantStruct::get(ClassnfABITy, Values);
      GlobalVariable *GV = GetClassGlobal(ClassName, Weak);
      GV->setInitializer(Init);
      GV->setSection("__DATA, __objc_data");
      GV->setAlignment(MD->getDataLayout().getABITypeAlignment(ClassnfABITy));
      if (HiddenVisibility) GV->setVisibility(GlobalValue::HiddenVisibility);
      
      return GV;
    }
    
    GlobalVariable *createMorphling(StringRef ClassName, Function *LoadMethod) {
      GlobalVariable *MetaGV, *ClassGV;
      GlobalVariable *SuperClassGV, *IsAGV, *CLASS_RO_GV;
      unsigned flags = 0;
      
      SmallString<64> TMetaName(getMetaclassSymbolPrefix());
      TMetaName += ClassName;
      SmallString<64> TClassName(getClassSymbolPrefix());
      TClassName += ClassName;
      
      /* meta */ {
        flags = NonFragileABI_Class_Meta | NonFragileABI_Class_Root;
        IsAGV = GetClassGlobal(TMetaName.str(), false);
        SuperClassGV = GetClassGlobal(TClassName.str(), false);
        std::vector<Constant*> Methods;
        Methods.push_back(GetMethodConstant(LoadMethod, "load", "v8@0:4"));
        CLASS_RO_GV = BuildClassRoTInitializer(flags, ClassName, Methods);
        MetaGV = BuildClassMetaData(TMetaName.str(), IsAGV, SuperClassGV, CLASS_RO_GV, true, false);
      }
      
      /* class */ {
        flags = NonFragileABI_Class_Root;
        SuperClassGV = nullptr;
        std::vector<Constant*> Methods;
        CLASS_RO_GV = BuildClassRoTInitializer(flags, ClassName, Methods);
        ClassGV = BuildClassMetaData(TClassName.str(), MetaGV, SuperClassGV, CLASS_RO_GV, true, false);
      }
      
      return ClassGV;
    }
    
    GlobalVariable *GetClassGlobal(const std::string &Name, bool Weak) {
      GlobalValue::LinkageTypes L = GlobalValue::LinkOnceODRLinkage;
      GlobalVariable *GV = MD->getGlobalVariable(Name, true);
      if (!GV) GV = new GlobalVariable(*MD, ClassnfABITy ,false, L, nullptr, Name);
      assert(GV->getLinkage() == L);
      return GV;
    }
    
    bool ObjCNonFragileABITypesHelper(Module &M) {
      LLVMContext &VMContext = M.getContext();
      
      MD = &M;
      ObjCABI = 2;
      
      ObjCEmptyCacheVar = M.getGlobalVariable("_objc_empty_cache", true);
      if (!ObjCEmptyCacheVar)
        return false;
      
      ObjCEmptyVtableVar = M.getGlobalVariable("_objc_empty_vtable", true);
      
      Int32Ty = Type::getInt32Ty(VMContext);
      Type *Int8Ty = Type::getInt8Ty(VMContext);
      PtrTy = PointerType::getUnqual(Int8Ty);
      ObjectPtrTy = PointerType::getUnqual(Int8Ty);
      SelectorPtrTy = PointerType::getUnqual(Int8Ty);
      
      CacheTy = M.getTypeByName("struct._objc_cache");
      CachePtrTy = PointerType::getUnqual(CacheTy);
      
      Type *params[] = {ObjectPtrTy, SelectorPtrTy};
      ImpnfABITy = FunctionType::get(ObjectPtrTy, params, false)->getPointerTo();
      
      ClassnfABITy = M.getTypeByName("struct._class_t");
      ClassnfABIPtrTy = PointerType::getUnqual(ClassnfABITy);
      ClassRonfABITy = M.getTypeByName("struct._class_ro_t");
      
      /* method */
      MethodTy = M.getTypeByName("struct._objc_method");
      MethodListnfABITy = M.getTypeByName("struct.__method_list_t");
      MethodListnfABIPtrTy = PointerType::getUnqual(MethodListnfABITy);
      /* protocol */
      ProtocolnfABITy = M.getTypeByName("struct._protocol_t");
      ProtocolnfABIPtrTy = PointerType::getUnqual(ProtocolnfABITy);
      ProtocolListnfABITy = M.getTypeByName("struct._objc_protocol_list");
      ProtocolListnfABIPtrTy = PointerType::getUnqual(ProtocolListnfABITy);
      /* ivar */
      IvarnfABITy = M.getTypeByName("struct._ivar_t");
      IvarListnfABITy = M.getTypeByName("struct._ivar_list_t");
      IvarListnfABIPtrTy = PointerType::getUnqual(IvarListnfABITy);
      /* prop */
      PropertyTy = M.getTypeByName("struct._prop_t");
      PropertyListTy = M.getTypeByName("struct._prop_list_t");
      PropertyListPtrTy = PointerType::getUnqual(PropertyListTy);
      
      return true;
    }
    
    const char *getMetaclassSymbolPrefix() const {
      return "OBJC_METACLASS_$_";
    }
    
    const char *getClassSymbolPrefix() const {
      return "OBJC_CLASS_$_";
    }
    
    void addClassList(GlobalVariable* TClass, const char *SymbolName, const char *SectionName) {
      SmallVector<Constant*, 8> Symbols;
      Symbols.push_back(ConstantExpr::getBitCast(TClass, PtrTy));
      
      GlobalVariable *OGV = MD->getGlobalVariable(SymbolName, true);
      GlobalVariable *NGV = NULL;
      if (OGV) {
        ConstantArray *OldCA = cast<ConstantArray>(OGV->getInitializer());
        for (unsigned I = 0, E = OldCA->getNumOperands(); I < E; ++I)
          Symbols.push_back(OldCA->getOperand(I));
      }
      
      Constant *Init = ConstantArray::get(ArrayType::get(PtrTy, Symbols.size()), Symbols);
      NGV = new GlobalVariable(*MD, Init->getType(), false,
                               GlobalValue::PrivateLinkage,
                               Init, SymbolName);
      
      NGV->setAlignment(MD->getDataLayout().getABITypeAlignment(Init->getType()));
      NGV->setSection(SectionName);
      
      if (OGV) {
        NGV->takeName(OGV);
        if (!OGV->use_empty()) {
          Constant *V = NGV;
          if (V->getType() != OGV->getType())
            V = ConstantExpr::getBitCast(V, OGV->getType());
          OGV->replaceAllUsesWith(V);
        }
        OGV->eraseFromParent();
      }
      assert(NGV->getName() == SymbolName);
    }
  };
}

ModulePass *llvm::createLTOMorphlingPass() {
  (void)createMorphlingPass();
  return new LTOMorphling();
}

char LTOMorphling::ID = 0;
INITIALIZE_PASS(LTOMorphling, "acd", "Enable LTOMorphling.", true, true)
