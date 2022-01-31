#ifndef _STRING_OBFUSCATE_
#define _STRING_OBFUSCATE_

#include "llvm/IR/PassManager.h"

namespace llvm {
struct StringObfuscatePass : PassInfoMixin<StringObfuscatePass> {
public:
    PreservedAnalyses run(Module &M, ModuleAnalysisManager &);
};
}

#endif
