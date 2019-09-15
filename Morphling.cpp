
#include <sys/time.h>
#include <iostream>
#include "llvm/rapidjson/stringbuffer.h"
#include "llvm/rapidjson/writer.h"
#include <CoreFoundation/CoreFoundation.h>
#include "llvm/Transforms/Obfuscation/Morphling.h"
#include <fstream>
#include <random>

using namespace llvm;
using namespace std;

static cl::opt<std::string> AesSeed("aesSeed",
                                    cl::init(""),
                                    cl::desc("seed for the AES-CTR PRNG"));


int Morphling::sendMsg(std::string center, Variant& msg, Variant& output) {
  int status;
  CFMessagePortRef port;
  CFDataRef recv = nil;
  CFDataRef cfdata = nil;
  rp::StringBuffer buffer;
  rp::Writer<rapidjson::StringBuffer> writer(buffer);
  msg.Accept(writer);
  CFStringRef str = CFStringCreateWithCString(NULL, center.c_str(), kCFStringEncodingUTF8);
  
  port = CFMessagePortCreateRemote(NULL, str);
  if (!port || !CFMessagePortIsValid(port)) {
    status = kCFMessagePortIsInvalid;
    goto err;
  }
  
  cfdata = CFDataCreate(0, (const UInt8 *)buffer.GetString(), buffer.GetSize());
  status = CFMessagePortSendRequest(port, 0, cfdata, 5, 5, kCFRunLoopDefaultMode, &recv);
  if (status != kCFMessagePortSuccess)
    goto err;
  
  if (recv && CFDataGetLength(recv)) {
    CFStringRef recv_str = CFStringCreateFromExternalRepresentation(NULL, recv, kCFStringEncodingUTF8);
    output.Parse(CFStringGetCStringPtr(recv_str, kCFStringEncodingUTF8));
    if (recv_str) CFRelease(recv_str);
  }
  
  goto ret;
err:
  
ret:
  if (str) CFRelease(str);
  if (port) CFRelease(port);
  if (cfdata) CFRelease(cfdata);
  if (recv) CFRelease(recv);
  
  return status;
}

llvm::GlobalVariable *Morphling::getCString(Module& M, StringRef string) {
  llvm::Constant *Value = llvm::ConstantDataArray::getString(M.getContext(), string, true);
  llvm::GlobalVariable *GV = new llvm::GlobalVariable(M, Value->getType(), true,
                                                      llvm::GlobalValue::PrivateLinkage, Value);
  return GV;
}

int Morphling::postMsg(std::string center, Variant& msg) {
  int status;
  CFMessagePortRef port;
  CFDataRef recv = nil;
  CFDataRef cfdata = nil;
  rp::StringBuffer buffer;
  rp::Writer<rapidjson::StringBuffer> writer(buffer);
  msg.Accept(writer);
  CFStringRef str = CFStringCreateWithCString(NULL, center.c_str(), kCFStringEncodingUTF8);
  
  port = CFMessagePortCreateRemote(NULL, str);
  if (!port || !CFMessagePortIsValid(port)) {
    status = kCFMessagePortIsInvalid;
    goto err;
  }
  
  cfdata = CFDataCreate(0, (const UInt8 *)buffer.GetString(), buffer.GetSize());
  status = CFMessagePortSendRequest(port, 1, cfdata, 5, 0, 0, &recv);
  if (status != kCFMessagePortSuccess)
    goto err;
  
  goto ret;
err:
  
ret:
  if (str) CFRelease(str);
  if (port) CFRelease(port);
  if (cfdata) CFRelease(cfdata);
  if (recv) CFRelease(recv);
  
  return status;
}

std::string Morphling::readAnnotate(Function *f) {
  std::string annotation = "";
  
  GlobalVariable *glob = f->getParent()->getGlobalVariable("llvm.global.annotations");
  if (!glob)
    return annotation;
  
  ConstantArray *ca = dyn_cast<ConstantArray>(glob->getInitializer());
  if (!ca)
    return annotation;
  
  for (unsigned i = 0; i < ca->getNumOperands(); ++i) {
    ConstantStruct *structAn = dyn_cast<ConstantStruct>(ca->getOperand(i));
    if (!structAn)
      continue;
    ConstantExpr *expr = dyn_cast<ConstantExpr>(structAn->getOperand(0));
    if (!expr)
      continue;
    
    if (expr->getOpcode() != Instruction::BitCast || expr->getOperand(0) == f)
      continue;
    
    ConstantExpr *note = cast<ConstantExpr>(structAn->getOperand(1));
    if (!note || note->getOpcode() != Instruction::GetElementPtr)
      continue;
    
    GlobalVariable *noteStr = dyn_cast<GlobalVariable>(note->getOperand(0));
    if (!noteStr)
      continue;
    
    ConstantDataSequential *data = dyn_cast<ConstantDataSequential>(noteStr->getInitializer());
    if (!data)
      continue;
    
    if (!data->isString())
      continue;
    
    annotation += data->getAsString().lower() + " ";
  }
  return annotation;
}


bool Morphling::toObfuscate(bool flag, Function *f, std::string attr) {
  if (f->isDeclaration())
    return false;
  if (f->hasAvailableExternallyLinkage() != 0)
    return false;
  if (readAnnotate(f).find("no" + attr) != std::string::npos)
    return false;
  if (readAnnotate(f).find(attr) != std::string::npos)
    return true;
  return flag;
}


StringRef Morphling::getPassName() const {
  return StringRef("Morphling");
}

std::vector<std::string> Morphling::split(std::string str, std::string pattern) {
  std::string::size_type pos;
  std::vector<std::string> result;
  str += pattern;
  size_t size = str.size();
  
  for(size_t i = 0; i < size; i++) {
    pos = str.find(pattern,i);
    if(pos < size) {
      std::string s = str.substr(i, pos - i);
      result.push_back(s);
      i = pos + pattern.size() - 1;
    }
  }
  return result;
}

rp::Value Morphling::getConfig(std::string key) {
  rp::Value null;
  if (!configs) {
    Variant packet(rapidjson::kObjectType);
    Allocator &al = packet.GetAllocator();
    packet.AddMember("cmd", "config", al);
    Variant reply;
    if (Morphling::sendMsg("morphling", packet, reply) == kCFMessagePortSuccess) {
      configs = new Variant();
      configs->Swap(reply);
    }
  }
  
  if (!configs)
    return null;
  
  rp::Value config(*configs, configs->GetAllocator());
  std::vector<std::string> paths = split(key, ".");
  for (unsigned i = 0; i < paths.size(); i++) {
    if (!config.HasMember(paths[i].c_str()))
      return null;
    config = config.FindMember(paths[i].c_str())->value.GetObject();
  }
  
  return config;
}

bool Morphling::centerIsAlive() {
  std::string pong = "pong";
  bool alive = false;
  Variant packet(rapidjson::kObjectType);
  Allocator &al = packet.GetAllocator();
  packet.AddMember("cmd", "ping", al);
  Variant reply;
  int status = Morphling::sendMsg("morphling", packet, reply);
  if (status == kCFMessagePortSuccess) {
    if (reply.IsObject() &&
        reply.HasMember("cmd") &&
        pong.compare(reply.FindMember("cmd")->value.GetString()) == 0)
      alive = true;
  }
  return alive;
}

static
bool loadFileList(const char* filelist, std::vector<std::string>& files) {
  std::ifstream input(filelist);
  if (!input.is_open())
    return false;
  std::string line;
  while(getline(input, line))
    files.push_back(line);
  input.close();
  return true;
}

static
void writeFileList(const char* filelist, std::vector<std::string>& files) {
  std::ofstream os(filelist);
  for (auto file : files)
    os << file << "\n";
}


void Morphling::solveFilelist(const char* path) {
  Variant packet(rp::kObjectType);
  Allocator &al = packet.GetAllocator();
  packet.AddMember("cmd", "filelist", al);
  rp::Value parms(rp::kObjectType);
  parms.AddMember("pid", getpid(), al);
  parms.AddMember("from", "clang", al);
  parms.AddMember("path", rp::StringRef(path), al);
  packet.AddMember("parms", parms, al);
  Variant reply;
  int status = Morphling::sendMsg("morphling", packet, reply);
  if (status == kCFMessagePortSuccess) {
    if (reply.FindMember("enable")->value.GetBool()) {
      std::vector<std::string> files;
      loadFileList(path, files);
      shuffle(files.begin(), files.end(), std::default_random_engine(getpid()));
      writeFileList(path, files);
    }
  }
}

static
bool compare(const Value &L, const Value &R) {
  return (llvm::cryptoutils->get_range(INT8_MAX) % 2);
}

void Morphling::solveSymbol(Module &M) {
  M.getGlobalList().sort(compare);
  M.getFunctionList().sort(compare);
  M.getAliasList().sort(compare);
  M.getIFuncList().sort(compare);
}


void Morphling::solveRegister(std::vector<MCPhysReg>& ao) {
  if (seed) {
    rp::Value sortobf = Morphling::getConfig("obfuscation.sortobf");
    if (sortobf.HasMember("register") &&
        sortobf.FindMember("register")->value.GetBool()) {
      std::shuffle(ao.begin(), ao.end(), std::default_random_engine(seed));
    }
  }
}


bool Morphling::runOnModule(Module &M) {
  if (!Morphling::centerIsAlive())
    M.getContext().diagnose(MorphlingDiagnosticInfo("morphling is not alive!"));

  rp::Value sortobf = Morphling::getConfig("obfuscation.sortobf");
  if (sortobf.HasMember("symbol") &&
      sortobf.FindMember("symbol")->value.GetBool())
    Morphling::solveSymbol(M);
  
  rp::Value config = Morphling::getConfig("obfuscation");
  
  for (Module::iterator iter = M.begin(); iter != M.end(); iter++) {
    Function &F = *iter;
    if (!F.isDeclaration()) {
      FunctionPass *P = NULL;
      if (config.HasMember("bcfobf")) {
        P = createBogusControlFlowPass(true);
        P->runOnFunction(F);
        delete P;
      }
    }
  }
  
  if (config.HasMember("inbobf")) {
    FunctionPass *P = createIndirectBranchPass(true);
    vector<Function *> funcs;
    for (Module::iterator iter = M.begin(); iter != M.end(); iter++)
      funcs.push_back(&*iter);
    for (Function *F : funcs)
      P->runOnFunction(*F);
    delete P;
  }
  
  return true;
}


ModulePass *llvm::createMorphlingPass() {
  if (Morphling::centerIsAlive())
    Morphling::seed = Morphling::getConfig("obfuscation.seed").GetInt();
  return new Morphling();
}


char Morphling::ID = 0;
int Morphling::seed = 0;
Variant* Morphling::configs = NULL;
INITIALIZE_PASS_BEGIN(Morphling, "morphling", "Enable Morphling", true, true)
INITIALIZE_PASS_DEPENDENCY(IndirectBranch);
INITIALIZE_PASS_DEPENDENCY(BogusControlFlow);
INITIALIZE_PASS_DEPENDENCY(StringEncryption);
INITIALIZE_PASS_DEPENDENCY(Substitution);
INITIALIZE_PASS_END(Morphling, "morphling", "Enable Morphling", true, true)
