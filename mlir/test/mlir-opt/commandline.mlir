// RUN: mlir-opt --show-dialects | FileCheck %s
// CHECK: Available Dialects:
// CHECK-NEXT: acc
// CHECK-NEXT: affine
// CHECK-NEXT: amx
// CHECK-NEXT: arm_neon
// CHECK-NEXT: arm_sve
// CHECK-NEXT: async
// CHECK-NEXT: complex
// CHECK-NEXT: dlti
// CHECK-NEXT: emitc
// CHECK-NEXT: gpu
// CHECK-NEXT: linalg
// CHECK-NEXT: llvm
// CHECK-NEXT: math
// CHECK-NEXT: memref
// CHECK-NEXT: nvvm
// CHECK-NEXT: omp
// CHECK-NEXT: pdl
// CHECK-NEXT: pdl_interp
// CHECK-NEXT: quant
// CHECK-NEXT: rocdl
// CHECK-NEXT: scf
// CHECK-NEXT: shape
// CHECK-NEXT: sparse_tensor
// CHECK-NEXT: spv
// CHECK-NEXT: std
// CHECK-NEXT: tensor
// CHECK-NEXT: test
// CHECK-NEXT: tosa
// CHECK-NEXT: vector
// CHECK-NEXT: x86vector