#include "llvm/Pass.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Obfuscation/StringObfuscate.h"
#include "llvm/Transforms/Obfuscation/CryptoUtils.h"
#include <string>
#include <vector>
#include <cstdlib>
#include <ctime>
#include <strstream>

using std::strstream;
using std::string;
using std::vector;
using std::pair;
using namespace llvm;

#define MAX_RAND 32767
vector<GlobalVariable*> Orig_Gv;
vector<pair<GlobalVariable*, ConstantInt*>> Ecry_Data;

static void obfuscateString(Module &M, User *Global_Usr, GlobalVariable *Global_Var) {
  if(!Global_Var->hasInitializer()){
    return;
  }
  ConstantDataSequential *contant_result = NULL;
  if(Global_Var->getSection() != StringRef("llvm.metadata") && Global_Var->getSection().find(StringRef("__objc")) == string::npos && Global_Var->getName().find("OBJC") == string::npos) {
    if(isa<ConstantStruct>(Global_Var->getInitializer()) && StructType::getTypeByName(M.getContext(), StringRef("struct.__NSConstantString_tag"))!=NULL) { //
        ConstantStruct* CTS = dyn_cast<ConstantStruct>(Global_Var->getInitializer());
        if(CTS->getType() != StructType::getTypeByName(M.getContext(), StringRef("struct.__NSConstantString_tag"))){
              return;
        }
        GlobalVariable *str_contant = dyn_cast<GlobalVariable>(CTS->getOperand(2)->stripPointerCasts());
        contant_result = dyn_cast<ConstantDataSequential>(str_contant->getInitializer());
        for(User *t_usr : str_contant->users()) {
          Global_Usr = t_usr;
          Global_Var = str_contant;
          break;
        }
    } else if(isa<ConstantDataSequential>(Global_Var->getInitializer())) {
        contant_result = dyn_cast<ConstantDataSequential>(Global_Var->getInitializer());
    }
  } else if(isa<ConstantDataArray>(Global_Var->getInitializer())) {
    contant_result = dyn_cast<ConstantDataArray>(Global_Var->getInitializer());
  }
  if (contant_result == nullptr) {
    return;
  }

  if(IntegerType *elementType = dyn_cast<IntegerType>(contant_result->getElementType())) {
      ConstantInt *key = NULL;
      Constant *encrypcons = NULL;
      int numElements = (int)(contant_result->getNumElements());
      if(elementType == Type::getInt8Ty(M.getContext())) {
          vector<uint8_t> encrypt_elements;
          uint8_t key_num = cryptoutils->get_uint8_t();
          for(int i = 0; i < numElements; i++) {
            uint64_t char_c = contant_result->getElementAsInteger(i);
            encrypt_elements.push_back(char_c ^ key_num);
          }
          key = ConstantInt::get(Type::getInt8Ty(M.getContext()), key_num);
          encrypcons = ConstantDataArray::get(M.getContext(), ArrayRef<uint8_t>(encrypt_elements));
      } else if(elementType == Type::getInt16Ty(M.getContext())) {
          vector<uint16_t> encrypt_elements;
          uint16_t key_num = (uint16_t)(cryptoutils->get_uint64_t());
          for(int i = 0; i < numElements; i++) {
            uint64_t char_c = contant_result->getElementAsInteger(i);
            encrypt_elements.push_back(char_c ^ key_num);
          }
          key = ConstantInt::get(Type::getInt16Ty(M.getContext()), key_num);
          encrypcons = ConstantDataArray::get(M.getContext(), ArrayRef<uint16_t>(encrypt_elements));
      } else {
        errs() << "other type" << "\n";
      }
      GlobalVariable *Encryp_Gv = new GlobalVariable(*(Global_Var->getParent()), encrypcons->getType(), false,
                                                        Global_Var->getLinkage(), encrypcons, "encryp_gv", nullptr,
                                                        Global_Var->getThreadLocalMode(), Global_Var->getType()->getAddressSpace());
      Global_Usr->replaceUsesOfWith(Global_Var, Encryp_Gv);
      Ecry_Data.push_back(pair<GlobalVariable*, ConstantInt*>(Encryp_Gv, key));
      Orig_Gv.push_back(Global_Var);
  }
}

static string getDecryptFuncName() {
    uint64_t StringObfDecodeRandomName = cryptoutils->get_uint64_t();
    string  random_str;
    strstream random_stream;
    random_stream << StringObfDecodeRandomName;
    random_stream >> random_str;
    StringObfDecodeRandomName++;
    return "sub_" + random_str;
}

static void insertDecryptFunc(Module &M) {
  if(Ecry_Data.size() == 0) {
    return;
  }
  LLVMContext &context = M.getContext();
  IRBuilder<> builder(context);

  Type *voidTy = builder.getVoidTy();
  SmallVector<Type*, 0> FuncArgs = {};
  FunctionType *decry_func_type = FunctionType::get(voidTy, FuncArgs, false);
  FunctionCallee decry_func_callee = M.getOrInsertFunction(StringRef(getDecryptFuncName()), decry_func_type);
  Function *decry_str_func = cast<Function>(decry_func_callee.getCallee());
  decry_str_func->setCallingConv(CallingConv::C);

  BasicBlock *decry_str_entryBB = BasicBlock::Create(context, "decry_str_entryBB", decry_str_func);
  builder.SetInsertPoint(decry_str_entryBB);
  ConstantInt *zero = ConstantInt::get(Type::getInt32Ty(M.getContext()), 0);
  for(pair<GlobalVariable *, ConstantInt*> data : Ecry_Data) {
    GlobalVariable *Global_Var = data.first;
    ConstantInt *rand_key = data.second;
    ConstantDataSequential *CDS = cast<ConstantDataSequential>(Global_Var->getInitializer());
    int cds_numElements = (int)(CDS->getNumElements());
    for(int i = 0; i < cds_numElements; i++) {
      ConstantInt *offset = ConstantInt::get(Type::getInt32Ty(M.getContext()), i);
      Value *inBoundsGEP = builder.CreateInBoundsGEP(Global_Var->getType()->getElementType(), Global_Var, {zero, offset}, "inBoundsGEP");
      Value *char_c = builder.CreateLoad(inBoundsGEP->getType()->getPointerElementType(), inBoundsGEP, "char_c");
      Value *xor_value = builder.CreateXor(char_c, rand_key, "xor_value");
      builder.CreateStore(xor_value, inBoundsGEP, false);
    }
  }
  builder.CreateRetVoid();
  appendToGlobalCtors(M, decry_str_func, 0);
}

static void findGVUse(Module &M) {
  vector<GlobalValue*> All_Globals;
  for(GlobalValue &global : M.globals()) {
    All_Globals.push_back(&global);
  }

  for(GlobalValue *global : All_Globals) {
    GlobalVariable *Global_Var = dyn_cast<GlobalVariable>(global);
    if (Global_Var == nullptr) {
      continue;
    }
    User *Global_Usr = NULL;
    for (User *Usr : Global_Var->users()) {
      Instruction *Inst = dyn_cast<Instruction>(Usr);
      if (Inst == nullptr) {
        for (User *DirecUsr : Usr->users()) {
          if(CallInst *callInst = dyn_cast<CallInst>(DirecUsr)) {
             Global_Usr = Usr;
             obfuscateString(M, Global_Usr, Global_Var);
             break;
          }
        }
      }
    }
  }

  insertDecryptFunc(M);

  for(GlobalVariable *Gv : Orig_Gv) {
      Gv->eraseFromParent();
  }
}

PreservedAnalyses StringObfuscatePass::run(Module &M, ModuleAnalysisManager &MAM) {
  srand((unsigned)time(NULL));
  findGVUse(M);
  return PreservedAnalyses::none();
}
