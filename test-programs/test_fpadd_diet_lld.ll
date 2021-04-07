declare { i4, i1 } @llvm.uadd.with.overflow.i4(i4, i4)
declare { i8, i1 } @llvm.uadd.with.overflow.i8(i8, i8)
declare { i16, i1 } @llvm.uadd.with.overflow.i16(i16, i16)
declare { i32, i1 } @llvm.uadd.with.overflow.i32(i32, i32)
declare { i64, i1 } @llvm.uadd.with.overflow.i64(i64, i64)
declare { i4, i1 } @llvm.sadd.with.overflow.i4(i4, i4)
declare { i8, i1 } @llvm.sadd.with.overflow.i8(i8, i8)
declare { i16, i1 } @llvm.sadd.with.overflow.i16(i16, i16)
declare { i32, i1 } @llvm.sadd.with.overflow.i32(i32, i32)
declare { i64, i1 } @llvm.sadd.with.overflow.i64(i64, i64)
declare { i4, i1 } @llvm.usub.with.overflow.i4(i4, i4)
declare { i8, i1 } @llvm.usub.with.overflow.i8(i8, i8)
declare { i16, i1 } @llvm.usub.with.overflow.i16(i16, i16)
declare { i32, i1 } @llvm.usub.with.overflow.i32(i32, i32)
declare { i64, i1 } @llvm.usub.with.overflow.i64(i64, i64)
declare { i4, i1 } @llvm.ssub.with.overflow.i4(i4, i4)
declare { i8, i1 } @llvm.ssub.with.overflow.i8(i8, i8)
declare { i16, i1 } @llvm.ssub.with.overflow.i16(i16, i16)
declare { i32, i1 } @llvm.ssub.with.overflow.i32(i32, i32)
declare { i64, i1 } @llvm.ssub.with.overflow.i64(i64, i64)
declare i8 @llvm.cttz.i8(i8, i1)
declare i16 @llvm.cttz.i16(i16, i1)
declare i32 @llvm.cttz.i32(i32, i1)
declare i64 @llvm.cttz.i64(i64, i1)
declare i8 @llvm.ctlz.i8(i8, i1)
declare i16 @llvm.ctlz.i16(i16, i1)
declare i32 @llvm.ctlz.i32(i32, i1)
declare i64 @llvm.ctlz.i64(i64, i1)
define double @fpadd(double %arg0) {
block_0_201320:
  ; r0 := (bitcast arg0 (bv 64))
  %t0 = bitcast double %arg0 to i64
  ; r1 := (uext r0 512)
  %t1 = zext i64 %t0 to i512
  ; r2 := (trunc r1 64)
  %t2 = trunc i512 %t1 to i64
  ; r3 := (bitcast r2 double)
  %t3 = bitcast i64 %t2 to double
  ; r4 := (cvttsx2si 64 double r3)
  %t4 = fptosi double %t3 to i64
  ; r5 := (bv_add r4 (0x1 : bv 64))
  %t5 = add i64 %t4, 1
  ; r6 := (cvtsi2sx double 64 r5)
  %t6 = sitofp i64 %t5 to double
  ; r7 := (bitcast arg0 (bv 64))
  %t7 = bitcast double %arg0 to i64
  ; r8 := (uext r7 512)
  %t8 = zext i64 %t7 to i512
  ; r9 := (bv_and r8 (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : bv 512))
  %t9 = and i512 %t8, 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946551499689575296532480
  ; r10 := (bitcast r6 (bv 64))
  %t10 = bitcast double %t6 to i64
  ; r11 := (uext r10 512)
  %t11 = zext i64 %t10 to i512
  ; r12 := (bv_or r9 r11)
  %t12 = or i512 %t9, %t11
  ; r13 := (trunc r12 64)
  %t13 = trunc i512 %t12 to i64
  ; r14 := (bitcast r13 double)
  %t14 = bitcast i64 %t13 to double
  ret double %t14
}
define i64 @main() {
block_0_201350:
  ; r0 := (read (0x200190 : bv 64) (bv 64))
  %t0 = inttoptr i64 2097552 to i64*
  %t1 = load i64, i64* %t0
  ; r1 := (bv_and undef (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000 : bv 512))
  %t2 = and i512 undef, 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186485710571386961873483106571826217237872640
  ; r2 := (uext r0 512)
  %t3 = zext i64 %t1 to i512
  ; r3 := (bv_or r1 r2)
  %t4 = or i512 %t2, %t3
  ; r4 := (trunc r3 64)
  %t5 = trunc i512 %t4 to i64
  ; r5 := (bitcast r4 double)
  %t6 = bitcast i64 %t5 to double
  ; r6 := call fpadd(r5)
  %t7 = call double (double) @fpadd(double %t6)
  ; r7 := (bitcast r6 (bv 64))
  %t8 = bitcast double %t7 to i64
  ; r8 := (uext r7 512)
  %t9 = zext i64 %t8 to i512
  br label %block_0_20136c
block_0_20136c:
  ret i64 0
}