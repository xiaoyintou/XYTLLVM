; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc -mtriple x86_64 < %s | FileCheck %s

; To ensure unused floating point constant is correctly removed
define float @test(float %src, float* %p) {
; CHECK-LABEL: test:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    movq $0, (%rdi)
; CHECK-NEXT:    xorps %xmm0, %xmm0
; CHECK-NEXT:    retq
entry:
  %a0 = getelementptr inbounds float, float* %p, i32 0
  %a1 = getelementptr inbounds float, float* %p, i32 1
  store float 0.000000e+00, float* %a0
  store float 0.000000e+00, float* %a1
  %zero = load float, float* %a0
  %fmul1 = fmul fast float %zero, %src
  %fadd1 = fadd fast float %fmul1, %zero
  %fmul2 = fmul fast float %fadd1, 2.000000e+00
  %fmul3 = fmul fast float %fmul2, %fmul2
  %fmul4 = fmul fast float %fmul2, 2.000000e+00
  %fadd2 = fadd fast float %fmul4, -3.000000e+00
  %fmul5 = fmul fast float %fadd2, %fmul2
  %fadd3 = fadd fast float %fmul2, %src
  %fadd4 = fadd fast float %fadd3, %fmul5
  %fmul6 = fmul fast float %fmul3, %fadd4
  ret float %fmul6
}

; To ensure negated result will not be removed when NegX=NegY and
; NegX is needed
define float @test2(float %x, float %y) {
; CHECK-LABEL: test2:
; CHECK:       # %bb.0:
; CHECK-NEXT:    movaps %xmm1, %xmm0
; CHECK-NEXT:    mulss {{\.?LCPI[0-9]+_[0-9]+}}(%rip), %xmm0
; CHECK-NEXT:    retq
  %add = fadd fast float %x, 750.0
  %sub = fsub fast float %x, %add
  %mul = fmul fast float %sub, %sub
  %mul2 = fmul fast float %mul, %sub
  %add2 = fadd fast float %mul2, 1.0
  %add3 = fadd fast float %mul2, %add2
  %mul3 = fmul fast float %y, %add3
  ret float %mul3
}