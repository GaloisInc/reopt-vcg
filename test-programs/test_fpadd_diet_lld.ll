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
define void @fpadd(<8 x double> %arg0) {
block_0_201320:
  ; r0 := (bitcast arg0 (bv 512))
  %t0 = bitcast <8 x double> %arg0 to i512
  ; r1 := (trunc r0 64)
  %t1 = trunc i512 %t0 to i64
  ; r2 := (bitcast r1 double)
  %t2 = bitcast i64 %t1 to double
  ; r3 := (cvttsx2si 64 double r2)
  %t3 = fptosi double %t2 to i64
  ; r4 := (bv_add r3 (0x1 : bv 64))
  %t4 = add i64 %t3, 1
  ; r5 := (cvtsi2sx double 64 r4)
  %t5 = sitofp i64 %t4 to double
  ret void
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
  ; r4 := (bitcast r3 (vec 8 double))
  %t5 = bitcast i512 %t4 to <8 x double>
  ; call fpadd(r4)
  call void (<8 x double>) @fpadd(<8 x double> %t5)
  br label %block_0_20136c
block_0_20136c:
  ret i64 0
}