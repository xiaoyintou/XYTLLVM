// RUN: mlir-opt -convert-memref-to-llvm %s | FileCheck %s

// CHECK-LABEL: @empty
func @empty() {
  // CHECK: llvm.intr.stacksave 
  // CHECK: llvm.br
  memref.alloca_scope {
    memref.alloca_scope.return
  }
  // CHECK: llvm.intr.stackrestore 
  // CHECK: llvm.br
  return
}

// CHECK-LABEL: @returns_nothing
func @returns_nothing(%b: f32) {
  %a = constant 10.0 : f32
  // CHECK: llvm.intr.stacksave 
  memref.alloca_scope {
    %c = std.addf %a, %b : f32
    memref.alloca_scope.return
  }
  // CHECK: llvm.intr.stackrestore 
  return
}

// CHECK-LABEL: @returns_one_value
func @returns_one_value(%b: f32) -> f32 {
  %a = constant 10.0 : f32
  // CHECK: llvm.intr.stacksave 
  %result = memref.alloca_scope -> f32 {
    %c = std.addf %a, %b : f32
    memref.alloca_scope.return %c: f32
  }
  // CHECK: llvm.intr.stackrestore 
  return %result : f32
}

// CHECK-LABEL: @returns_multiple_values
func @returns_multiple_values(%b: f32) -> f32 {
  %a = constant 10.0 : f32
  // CHECK: llvm.intr.stacksave 
  %result1, %result2 = memref.alloca_scope -> (f32, f32) {
    %c = std.addf %a, %b : f32
    %d = std.subf %a, %b : f32
    memref.alloca_scope.return %c, %d: f32, f32
  }
  // CHECK: llvm.intr.stackrestore 
  %result = std.addf %result1, %result2 : f32
  return %result : f32
}
