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
define i64 @add(i64 %arg0) {
block_0_201320:
  ; r0 := (bv_add arg0 (0x1 : bv 64))
  %t0 = add i64 %arg0, 1
  ret i64 %t0
}
define i64 @main() {
block_0_201340:
  ; r0 := call add((0x2a : bv 64))
  %t0 = call i64 (i64) @add(i64 42)
  br label %block_0_201359
block_0_201359:
  ret i64 0
}
define void @__you_tried_to_link_a_dietlibc_object_against_glibc() {
block_0_2013a9:
  ret void
}
define { i64, i64 } @reopt_find_in_auxvec_0_0x2013bb(i64 %arg0, i64 %arg1, i64 %arg2) {
block_0_2013bb:
  ; r0 := (read arg0 (bv 64))
  %t0 = inttoptr i64 %arg0 to i64*
  %t1 = load i64, i64* %t0
  ; r1 := (eq r0 (0x0 : bv 64))
  %t2 = icmp eq i64 %t1, 0
  br i1 %t2, label %block_0_2013d3, label %block_0_2013c3
block_0_2013c3:
  %t3 = phi i64 [ %t1, %block_0_2013bb ]
  %t4 = phi i64 [ %arg2, %block_0_2013bb ]
  %t5 = phi i64 [ %arg1, %block_0_2013bb ]
  %t6 = phi i64 [ %arg0, %block_0_2013bb ]
  ; r6 := (eq r2 r4)
  %t7 = icmp eq i64 %t3, %t5
  br i1 %t7, label %block_0_2013c8, label %block_0_2013cd
block_0_2013c8:
  %t8 = phi i64 [ %t4, %block_0_2013c3 ]
  %t9 = phi i64 [ %t6, %block_0_2013c3 ]
  ; r9 := (bv_add r8 (0x8 : bv 64))
  %t10 = add i64 %t9, 8
  ; r10 := (read r9 (bv 64))
  %t11 = inttoptr i64 %t10 to i64*
  %t12 = load i64, i64* %t11
  ; r11 := (tuple r10 r7)
  %t13 = insertvalue { i64, i64 } undef, i64 %t12, 0
  %t14 = insertvalue { i64, i64 } %t13, i64 %t8, 1
  ret { i64, i64 } %t14
block_0_2013cd:
  %t15 = phi i64 [ %t4, %block_0_2013c3 ]
  %t16 = phi i64 [ %t5, %block_0_2013c3 ]
  %t17 = phi i64 [ %t6, %block_0_2013c3 ]
  ; r15 := (bv_add r14 (0x10 : bv 64))
  %t18 = add i64 %t17, 16
  %t19 = call { i64, i64 } (i64, i64, i64) @reopt_find_in_auxvec_0_0x2013bb(i64 %t18, i64 %t16, i64 %t15)
  ret { i64, i64 } %t19
block_0_2013d3:
  %t20 = phi i64 [ %t1, %block_0_2013bb ]
  %t21 = phi i64 [ %arg2, %block_0_2013bb ]
  ; r18 := (tuple r16 r17)
  %t22 = insertvalue { i64, i64 } undef, i64 %t20, 0
  %t23 = insertvalue { i64, i64 } %t22, i64 %t21, 1
  ret { i64, i64 } %t23
}
define void @reopt_getauxval_0_0x201406(i64 %arg0, i64 %arg1, i64 %arg2) {
block_0_201406:
  ; r0 := (read (0x202798 : bv 64) (bv 64))
  %t0 = inttoptr i64 2107288 to i64*
  %t1 = load i64, i64* %t0
  ; r1 := call reopt_find_in_auxvec_0_0x2013bb(r0, arg0, arg2)
  %t2 = call { i64, i64 } (i64, i64, i64) @reopt_find_in_auxvec_0_0x2013bb(i64 %t1, i64 %arg0, i64 %arg2)
  ret void
}