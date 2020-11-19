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
declare i64 @printf(i64, ...)
define i64 @fib(i64 %arg0) {
block_0_201000:
  ; r0 := (eq arg0 (0x1 : bv 64))
  %t0 = icmp eq i64 %arg0, 1
  ; r1 := (bv_ule (0x1 : bv 64) arg0)
  %t1 = icmp ule i64 1, %arg0
  ; r2 := (not r0)
  %t2 = icmp eq i1 %t0, 0
  ; r3 := (and r1 r2)
  %t3 = and i1 %t1, %t2
  br i1 %t3, label %block_0_201024, label %block_0_201017
block_0_201017:
  %t4 = phi i64 [ %arg0, %block_0_201000 ]
  br label %block_0_201058
block_0_201024:
  %t5 = phi i64 [ %arg0, %block_0_201000 ]
  ; r6 := (bv_add r5 (0xffffffffffffffff : bv 64))
  %t6 = add i64 %t5, 18446744073709551615
  ; (r7) := call fib(r6)
  %t7 = call i64 (i64) @fib(i64 %t6)
  br label %block_0_201036
block_0_201036:
  %t8 = phi i64 [ %t7, %block_0_201024 ]
  %t9 = phi i64 [ %t5, %block_0_201024 ]
  ; r10 := (bv_add r9 (0xfffffffffffffffe : bv 64))
  %t10 = add i64 %t9, 18446744073709551614
  ; (r11) := call fib(r10)
  %t11 = call i64 (i64) @fib(i64 %t10)
  br label %block_0_20104d
block_0_20104d:
  %t12 = phi i64 [ %t11, %block_0_201036 ]
  %t13 = phi i64 [ %t8, %block_0_201036 ]
  ; r14 := (bv_add r13 r12)
  %t14 = add i64 %t13, %t12
  br label %block_0_201058
block_0_201058:
  %t15 = phi i64 [ %t4, %block_0_201017 ], [ %t14, %block_0_20104d ]
  ret i64 %t15
}
define i64 @main() {
block_0_201070:
  ; (r0) := call fib((0x5 : bv 64))
  %t0 = call i64 (i64) @fib(i64 5)
  br label %block_0_201089
block_0_201089:
  %t1 = phi i64 [ %t0, %block_0_201070 ]
  ; (r2) := call printf((0x2001d2 : bv 64), r1)
  %t2 = call i64 (i64, ...) @printf(i64 2097618, i64 %t1)
  br label %block_0_20109d
block_0_20109d:
  ret i64 0
}