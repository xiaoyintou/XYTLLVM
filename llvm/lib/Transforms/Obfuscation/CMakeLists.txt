add_llvm_library( LLVMObfuscation
  CryptoUtils.cpp
  StringObfuscate.cpp

  DEPENDS
  intrinsics_gen
  )