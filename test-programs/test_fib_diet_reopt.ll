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
declare i64 @reopt_printf_0_0x2014aa(i64, ...)
define i64 @fib(i64 %arg0) {
block_0_201000:
  ; r0 := (bv_ult (0x1 : bv 64) arg0)
  %t0 = icmp ult i64 1, %arg0
  br i1 %t0, label %block_0_201024, label %block_0_201017
block_0_201017:
  %t1 = phi i64 [ %arg0, %block_0_201000 ]
  br label %block_0_201058
block_0_201024:
  %t2 = phi i64 [ %arg0, %block_0_201000 ]
  ; r3 := (bv_add r2 (0xffffffffffffffff : bv 64))
  %t3 = add i64 %t2, 18446744073709551615
  ; r4 := call fib(r3)
  %t4 = call i64 (i64) @fib(i64 %t3)
  br label %block_0_201036
block_0_201036:
  %t5 = phi i64 [ %t4, %block_0_201024 ]
  %t6 = phi i64 [ %t2, %block_0_201024 ]
  ; r7 := (bv_add r6 (0xfffffffffffffffe : bv 64))
  %t7 = add i64 %t6, 18446744073709551614
  ; r8 := call fib(r7)
  %t8 = call i64 (i64) @fib(i64 %t7)
  br label %block_0_20104d
block_0_20104d:
  %t9 = phi i64 [ %t8, %block_0_201036 ]
  %t10 = phi i64 [ %t5, %block_0_201036 ]
  ; r11 := (bv_add r10 r9)
  %t11 = add i64 %t10, %t9
  br label %block_0_201058
block_0_201058:
  %t12 = phi i64 [ %t1, %block_0_201017 ], [ %t11, %block_0_20104d ]
  ret i64 %t12
}
define i64 @main() {
block_0_201070:
  ; r0 := call fib((0x5 : bv 64))
  %t0 = call i64 (i64) @fib(i64 5)
  br label %block_0_201089
block_0_201089:
  %t1 = phi i64 [ %t0, %block_0_201070 ]
  ; r2 := call reopt_printf_0_0x2014aa((0x2001d2 : bv 64), r1)
  %t2 = call i64 (i64, ...) @reopt_printf_0_0x2014aa(i64 2097618, i64 %t1)
  br label %block_0_20109d
block_0_20109d:
  ret i64 0
}
define void @__you_tried_to_link_a_dietlibc_object_against_glibc() {
block_0_2010ec:
  ret void
}
define { i64, i64 } @reopt_find_in_auxvec_0_0x2010fe(i64 %arg0, i64 %arg1, i64 %arg2) {
block_0_2010fe:
  ; r0 := (read arg0 (bv 64))
  %t0 = inttoptr i64 %arg0 to i64*
  %t1 = load i64, i64* %t0
  ; r1 := (eq r0 (0x0 : bv 64))
  %t2 = icmp eq i64 %t1, 0
  br i1 %t2, label %block_0_201116, label %block_0_201106
block_0_201106:
  %t3 = phi i64 [ %t1, %block_0_2010fe ]
  %t4 = phi i64 [ %arg2, %block_0_2010fe ]
  %t5 = phi i64 [ %arg1, %block_0_2010fe ]
  %t6 = phi i64 [ %arg0, %block_0_2010fe ]
  ; r6 := (eq r2 r4)
  %t7 = icmp eq i64 %t3, %t5
  br i1 %t7, label %block_0_20110b, label %block_0_201110
block_0_20110b:
  %t8 = phi i64 [ %t4, %block_0_201106 ]
  %t9 = phi i64 [ %t6, %block_0_201106 ]
  ; r9 := (bv_add r8 (0x8 : bv 64))
  %t10 = add i64 %t9, 8
  ; r10 := (read r9 (bv 64))
  %t11 = inttoptr i64 %t10 to i64*
  %t12 = load i64, i64* %t11
  ; r11 := (tuple r10 r7)
  %t13 = insertvalue { i64, i64 } undef, i64 %t12, 0
  %t14 = insertvalue { i64, i64 } %t13, i64 %t8, 1
  ret { i64, i64 } %t14
block_0_201110:
  %t15 = phi i64 [ %t4, %block_0_201106 ]
  %t16 = phi i64 [ %t5, %block_0_201106 ]
  %t17 = phi i64 [ %t6, %block_0_201106 ]
  ; r15 := (bv_add r14 (0x10 : bv 64))
  %t18 = add i64 %t17, 16
  %t19 = call { i64, i64 } (i64, i64, i64) @reopt_find_in_auxvec_0_0x2010fe(i64 %t18, i64 %t16, i64 %t15)
  ret { i64, i64 } %t19
block_0_201116:
  %t20 = phi i64 [ %t1, %block_0_2010fe ]
  %t21 = phi i64 [ %arg2, %block_0_2010fe ]
  ; r18 := (tuple r16 r17)
  %t22 = insertvalue { i64, i64 } undef, i64 %t20, 0
  %t23 = insertvalue { i64, i64 } %t22, i64 %t21, 1
  ret { i64, i64 } %t23
}
define void @reopt_getauxval_0_0x201149(i64 %arg0, i64 %arg1, i64 %arg2) {
block_0_201149:
  ; r0 := (read (0x203030 : bv 64) (bv 64))
  %t0 = inttoptr i64 2109488 to i64*
  %t1 = load i64, i64* %t0
  ; r1 := call reopt_find_in_auxvec_0_0x2010fe(r0, arg0, arg2)
  %t2 = call { i64, i64 } (i64, i64, i64) @reopt_find_in_auxvec_0_0x2010fe(i64 %t1, i64 %arg0, i64 %arg2)
  ret void
}
define { i64, i64 } @reopt___isspace_ascii_0_0x20227d(i64 %arg0, i64 %arg1, i64 %arg2) {
block_0_20227d:
  ; r0 := (bv_add arg0 (0xfffffffffffffff7 : bv 64))
  %t0 = add i64 %arg0, 18446744073709551607
  ; r1 := (trunc r0 32)
  %t1 = trunc i64 %t0 to i32
  ; r2 := (bv_ule r1 (0x4 : bv 32))
  %t2 = icmp ule i32 %t1, 4
  ; r3 := (mux r2 (0x1 : bv 8) (0x0 : bv 8))
  %t3 = select i1 %t2, i8 1, i8 0
  ; r4 := (trunc arg0 32)
  %t4 = trunc i64 %arg0 to i32
  ; r5 := (eq r4 (0x20 : bv 32))
  %t5 = icmp eq i32 %t4, 32
  ; r6 := (mux r5 (0x1 : bv 8) (0x0 : bv 8))
  %t6 = select i1 %t5, i8 1, i8 0
  ; r7 := (bv_and arg2 (0xffffffffffffff00 : bv 64))
  %t7 = and i64 %arg2, 18446744073709551360
  ; r8 := (uext r6 64)
  %t8 = zext i8 %t6 to i64
  ; r9 := (bv_or r7 r8)
  %t9 = or i64 %t7, %t8
  ; r10 := (bv_or r3 r6)
  %t10 = or i8 %t3, %t6
  ; r11 := (uext r10 64)
  %t11 = zext i8 %t10 to i64
  ; r12 := (tuple r11 r9)
  %t12 = insertvalue { i64, i64 } undef, i64 %t11, 0
  %t13 = insertvalue { i64, i64 } %t12, i64 %t9, 1
  ret { i64, i64 } %t13
}
define void @reopt___lltostr_0_0x202396(i64 %arg0, i64 %arg1, i64 %arg2, i64 %arg3, i64 %arg4) {
block_0_202396:
  ; r0 := (bv_add arg1 (0xffffffffffffffff : bv 64))
  %t0 = add i64 %arg1, 18446744073709551615
  ; r1 := (trunc r0 32)
  %t1 = trunc i64 %t0 to i32
  ; r2 := (uext r1 64)
  %t2 = zext i32 %t1 to i64
  ; r3 := (bv_add arg3 (0xffffffffffffffff : bv 64))
  %t3 = add i64 %arg3, 18446744073709551615
  ; r4 := (trunc r3 32)
  %t4 = trunc i64 %t3 to i32
  ; r5 := (bv_add r2 arg0)
  %t5 = add i64 %t2, %arg0
  ; r6 := (bv_ule (0x24 : bv 32) r4)
  %t6 = icmp ule i32 36, %t4
  ; r7 := (trunc arg3 32)
  %t7 = trunc i64 %arg3 to i32
  ; r8 := (mux r6 (0xa : bv 32) r7)
  %t8 = select i1 %t6, i32 10, i32 %t7
  ; r9 := (uext r8 64)
  %t9 = zext i32 %t8 to i64
  ; r10 := (eq arg2 (0x0 : bv 64))
  %t10 = icmp eq i64 %arg2, 0
  ; write r5 (0x0 : bv 8)
  %t11 = inttoptr i64 %t5 to i8*
  store i8 0, i8* %t11
  br i1 %t10, label %block_0_2023ce, label %block_0_2023b8
block_0_2023b8:
  %t12 = phi i64 [ %arg2, %block_0_202396 ]
  %t13 = phi i64 [ %t9, %block_0_202396 ]
  %t14 = phi i64 [ %arg0, %block_0_202396 ]
  %t15 = phi i64 [ %arg4, %block_0_202396 ]
  %t16 = phi i64 [ %t5, %block_0_202396 ]
  ; r16 := (trunc r14 32)
  %t17 = trunc i64 %t15 to i32
  ; r17 := (bv_ult r16 (0x1 : bv 32))
  %t18 = icmp ult i32 %t17, 1
  ; r18 := (trunc r12 32)
  %t19 = trunc i64 %t13 to i32
  ; r19 := (uext r18 64)
  %t20 = zext i32 %t19 to i64
  ; r20 := (mux r17 (0xffffffff : bv 32) (0x0 : bv 32))
  %t21 = select i1 %t18, i32 4294967295, i32 0
  ; r21 := (bv_and r20 (0x20 : bv 32))
  %t22 = and i32 %t21, 32
  ; r22 := (bv_add r21 (0x7 : bv 32))
  %t23 = add i32 %t22, 7
  ; r23 := (uext r22 64)
  %t24 = zext i32 %t23 to i64
  br label %block_0_2023fb
block_0_2023ce:
  %t25 = phi i64 [ %arg0, %block_0_202396 ]
  %t26 = phi i64 [ %t5, %block_0_202396 ]
  ; r26 := (bv_add r25 (0xffffffffffffffff : bv 64))
  %t27 = add i64 %t26, 18446744073709551615
  ; write r26 (0x30 : bv 8)
  %t28 = inttoptr i64 %t27 to i8*
  store i8 48, i8* %t28
  br label %block_0_202405
block_0_2023de:
  %t29 = phi i64 [ %t57, %block_0_2023fb ]
  %t30 = phi i64 [ %t58, %block_0_2023fb ]
  %t31 = phi i64 [ %t66, %block_0_2023fb ]
  %t32 = phi i64 [ %t59, %block_0_2023fb ]
  %t33 = phi i64 [ %t60, %block_0_2023fb ]
  %t34 = phi i64 [ %t61, %block_0_2023fb ]
  %t35 = phi i64 [ %t62, %block_0_2023fb ]
  ; r34 := (eq r27 (0x0 : bv 64))
  %t36 = icmp eq i64 %t29, 0
  br i1 %t36, label %block_0_202405, label %block_0_2023e3
block_0_2023e3:
  %t37 = phi i64 [ %t29, %block_0_2023de ]
  %t38 = phi i64 [ %t30, %block_0_2023de ]
  %t39 = phi i64 [ %t32, %block_0_2023de ]
  %t40 = phi i64 [ %t33, %block_0_2023de ]
  %t41 = phi i64 [ %t34, %block_0_2023de ]
  %t42 = phi i64 [ %t35, %block_0_2023de ]
  ; r41 := (bv_add r37 (0xffffffffffffffff : bv 64))
  %t43 = add i64 %t39, 18446744073709551615
  ; r42 := (div 64 (0x0 : bv 64) r35 r36)
  %t44 = call { i64, i64 } (i64, i64, i64) asm sideeffect "div $4", "={ax},={dx},{dx},{ax},r,~{flags}"(i64 0, i64 %t37, i64 %t38)
  ; r43 := (tuple_field r42 0)
  %t45 = extractvalue { i64, i64 } %t44, 0
  ; r44 := (tuple_field r42 1)
  %t46 = extractvalue { i64, i64 } %t44, 1
  ; r45 := (trunc r44 32)
  %t47 = trunc i64 %t46 to i32
  ; r46 := (bv_add r45 (0x30 : bv 32))
  %t48 = add i32 %t47, 48
  ; r47 := (trunc r46 8)
  %t49 = trunc i32 %t48 to i8
  ; r48 := (uext r46 64)
  %t50 = zext i32 %t48 to i64
  ; r49 := (bv_add r39 r48)
  %t51 = add i64 %t41, %t50
  ; r50 := (trunc r49 32)
  %t52 = trunc i64 %t51 to i32
  ; r51 := (bv_ult (0x39 : bv 8) r47)
  %t53 = icmp ult i8 57, %t49
  ; r52 := (mux r51 r50 r46)
  %t54 = select i1 %t53, i32 %t52, i32 %t48
  ; r53 := (trunc r52 8)
  %t55 = trunc i32 %t54 to i8
  ; write r41 r53
  %t56 = inttoptr i64 %t43 to i8*
  store i8 %t55, i8* %t56
  br label %block_0_2023fb
block_0_2023fb:
  %t57 = phi i64 [ %t12, %block_0_2023b8 ], [ %t45, %block_0_2023e3 ]
  %t58 = phi i64 [ %t20, %block_0_2023b8 ], [ %t38, %block_0_2023e3 ]
  %t59 = phi i64 [ %t16, %block_0_2023b8 ], [ %t43, %block_0_2023e3 ]
  %t60 = phi i64 [ %t14, %block_0_2023b8 ], [ %t40, %block_0_2023e3 ]
  %t61 = phi i64 [ %t24, %block_0_2023b8 ], [ %t41, %block_0_2023e3 ]
  %t62 = phi i64 [ %t16, %block_0_2023b8 ], [ %t42, %block_0_2023e3 ]
  ; r60 := (trunc r59 32)
  %t63 = trunc i64 %t62 to i32
  ; r61 := (trunc r56 32)
  %t64 = trunc i64 %t59 to i32
  ; r62 := (bv_sub r60 r61)
  %t65 = sub i32 %t63, %t64
  ; r63 := (uext r62 64)
  %t66 = zext i32 %t65 to i64
  ; r64 := (bv_ult r57 r56)
  %t67 = icmp ult i64 %t60, %t59
  br i1 %t67, label %block_0_2023de, label %block_0_202405
block_0_202405:
  %t68 = phi i64 [ 1, %block_0_2023ce ], [ %t31, %block_0_2023de ], [ %t66, %block_0_2023fb ]
  %t69 = phi i64 [ %t27, %block_0_2023ce ], [ %t32, %block_0_2023de ], [ %t59, %block_0_2023fb ]
  %t70 = phi i64 [ %t25, %block_0_2023ce ], [ %t33, %block_0_2023de ], [ %t60, %block_0_2023fb ]
  ; r68 := (bv_add r65 (0x1 : bv 64))
  %t71 = add i64 %t68, 1
  ; r69 := (trunc r68 32)
  %t72 = trunc i64 %t71 to i32
  ; r70 := (uext r69 64)
  %t73 = zext i32 %t72 to i64
  ; call reopt_memmove_0_0x202411(r67, r66, r70)
  call void (i64, i64, i64) @reopt_memmove_0_0x202411(i64 %t70, i64 %t69, i64 %t73)
  br label %block_0_20240d
block_0_20240d:
  ret void
}
define void @reopt_memmove_0_0x202411(i64 %arg0, i64 %arg1, i64 %arg2) {
block_0_202411:
  ; r0 := (bv_ult arg0 arg1)
  %t0 = icmp ult i64 %arg0, %arg1
  ; r1 := (eq arg0 arg1)
  %t1 = icmp eq i64 %arg0, %arg1
  br i1 %t1, label %block_0_202441, label %block_0_202419
block_0_202419:
  %t2 = phi i64 [ %arg0, %block_0_202411 ]
  %t3 = phi i64 [ %arg2, %block_0_202411 ]
  %t4 = phi i64 [ %arg1, %block_0_202411 ]
  %t5 = phi i1 [ %t0, %block_0_202411 ]
  br i1 %t5, label %block_0_20241b, label %block_0_202430
block_0_20241b:
  %t6 = phi i64 [ %t2, %block_0_202419 ]
  %t7 = phi i64 [ %t3, %block_0_202419 ]
  %t8 = phi i64 [ %t4, %block_0_202419 ]
  br label %block_0_20241d
block_0_20241d:
  %t9 = phi i64 [ %t6, %block_0_20241b ], [ %t14, %block_0_202422 ]
  %t10 = phi i64 [ 0, %block_0_20241b ], [ %t23, %block_0_202422 ]
  %t11 = phi i64 [ %t7, %block_0_20241b ], [ %t16, %block_0_202422 ]
  %t12 = phi i64 [ %t8, %block_0_20241b ], [ %t17, %block_0_202422 ]
  ; r13 := (eq r11 r10)
  %t13 = icmp eq i64 %t11, %t10
  br i1 %t13, label %block_0_20242f, label %block_0_202422
block_0_202422:
  %t14 = phi i64 [ %t9, %block_0_20241d ]
  %t15 = phi i64 [ %t10, %block_0_20241d ]
  %t16 = phi i64 [ %t11, %block_0_20241d ]
  %t17 = phi i64 [ %t12, %block_0_20241d ]
  ; r18 := (bv_add r17 r15)
  %t18 = add i64 %t17, %t15
  ; r19 := (read r18 (bv 8))
  %t19 = inttoptr i64 %t18 to i8*
  %t20 = load i8, i8* %t19
  ; r20 := (bv_add r14 r15)
  %t21 = add i64 %t14, %t15
  ; write r20 r19
  %t22 = inttoptr i64 %t21 to i8*
  store i8 %t20, i8* %t22
  ; r21 := (bv_add r15 (0x1 : bv 64))
  %t23 = add i64 %t15, 1
  br label %block_0_20241d
block_0_20242f:
  ret void
block_0_202430:
  %t24 = phi i64 [ %t2, %block_0_202419 ], [ %t29, %block_0_202439 ]
  %t25 = phi i64 [ %t3, %block_0_202419 ], [ %t30, %block_0_202439 ]
  %t26 = phi i64 [ %t4, %block_0_202419 ], [ %t31, %block_0_202439 ]
  ; r25 := (bv_add r23 (0xffffffffffffffff : bv 64))
  %t27 = add i64 %t25, 18446744073709551615
  ; r26 := (eq r23 (0x0 : bv 64))
  %t28 = icmp eq i64 %t25, 0
  br i1 %t28, label %block_0_202441, label %block_0_202439
block_0_202439:
  %t29 = phi i64 [ %t24, %block_0_202430 ]
  %t30 = phi i64 [ %t27, %block_0_202430 ]
  %t31 = phi i64 [ %t26, %block_0_202430 ]
  ; r30 := (bv_add r29 r28)
  %t32 = add i64 %t31, %t30
  ; r31 := (read r30 (bv 8))
  %t33 = inttoptr i64 %t32 to i8*
  %t34 = load i8, i8* %t33
  ; r32 := (bv_add r27 r28)
  %t35 = add i64 %t29, %t30
  ; write r32 r31
  %t36 = inttoptr i64 %t35 to i8*
  store i8 %t34, i8* %t36
  br label %block_0_202430
block_0_202441:
  ret void
}
define void @reopt___ltostr_0_0x202442(i64 %arg0, i64 %arg1, i64 %arg2, i64 %arg3, i64 %arg4) {
block_0_202442:
  ; r0 := (bv_add arg1 (0xffffffffffffffff : bv 64))
  %t0 = add i64 %arg1, 18446744073709551615
  ; r1 := (trunc r0 32)
  %t1 = trunc i64 %t0 to i32
  ; r2 := (uext r1 64)
  %t2 = zext i32 %t1 to i64
  ; r3 := (bv_add arg3 (0xffffffffffffffff : bv 64))
  %t3 = add i64 %arg3, 18446744073709551615
  ; r4 := (trunc r3 32)
  %t4 = trunc i64 %t3 to i32
  ; r5 := (bv_add r2 arg0)
  %t5 = add i64 %t2, %arg0
  ; r6 := (bv_ule (0x24 : bv 32) r4)
  %t6 = icmp ule i32 36, %t4
  ; r7 := (trunc arg3 32)
  %t7 = trunc i64 %arg3 to i32
  ; r8 := (mux r6 (0xa : bv 32) r7)
  %t8 = select i1 %t6, i32 10, i32 %t7
  ; r9 := (uext r8 64)
  %t9 = zext i32 %t8 to i64
  ; r10 := (eq arg2 (0x0 : bv 64))
  %t10 = icmp eq i64 %arg2, 0
  ; write r5 (0x0 : bv 8)
  %t11 = inttoptr i64 %t5 to i8*
  store i8 0, i8* %t11
  br i1 %t10, label %block_0_20247a, label %block_0_202464
block_0_202464:
  %t12 = phi i64 [ %arg2, %block_0_202442 ]
  %t13 = phi i64 [ %t9, %block_0_202442 ]
  %t14 = phi i64 [ %arg0, %block_0_202442 ]
  %t15 = phi i64 [ %arg4, %block_0_202442 ]
  %t16 = phi i64 [ %t5, %block_0_202442 ]
  ; r16 := (trunc r14 32)
  %t17 = trunc i64 %t15 to i32
  ; r17 := (bv_ult r16 (0x1 : bv 32))
  %t18 = icmp ult i32 %t17, 1
  ; r18 := (trunc r12 32)
  %t19 = trunc i64 %t13 to i32
  ; r19 := (uext r18 64)
  %t20 = zext i32 %t19 to i64
  ; r20 := (mux r17 (0xffffffff : bv 32) (0x0 : bv 32))
  %t21 = select i1 %t18, i32 4294967295, i32 0
  ; r21 := (bv_and r20 (0x20 : bv 32))
  %t22 = and i32 %t21, 32
  ; r22 := (bv_add r21 (0x7 : bv 32))
  %t23 = add i32 %t22, 7
  ; r23 := (uext r22 64)
  %t24 = zext i32 %t23 to i64
  br label %block_0_2024a7
block_0_20247a:
  %t25 = phi i64 [ %arg0, %block_0_202442 ]
  %t26 = phi i64 [ %t5, %block_0_202442 ]
  ; r26 := (bv_add r25 (0xffffffffffffffff : bv 64))
  %t27 = add i64 %t26, 18446744073709551615
  ; write r26 (0x30 : bv 8)
  %t28 = inttoptr i64 %t27 to i8*
  store i8 48, i8* %t28
  br label %block_0_2024b1
block_0_20248a:
  %t29 = phi i64 [ %t57, %block_0_2024a7 ]
  %t30 = phi i64 [ %t58, %block_0_2024a7 ]
  %t31 = phi i64 [ %t66, %block_0_2024a7 ]
  %t32 = phi i64 [ %t59, %block_0_2024a7 ]
  %t33 = phi i64 [ %t60, %block_0_2024a7 ]
  %t34 = phi i64 [ %t61, %block_0_2024a7 ]
  %t35 = phi i64 [ %t62, %block_0_2024a7 ]
  ; r34 := (eq r27 (0x0 : bv 64))
  %t36 = icmp eq i64 %t29, 0
  br i1 %t36, label %block_0_2024b1, label %block_0_20248f
block_0_20248f:
  %t37 = phi i64 [ %t29, %block_0_20248a ]
  %t38 = phi i64 [ %t30, %block_0_20248a ]
  %t39 = phi i64 [ %t32, %block_0_20248a ]
  %t40 = phi i64 [ %t33, %block_0_20248a ]
  %t41 = phi i64 [ %t34, %block_0_20248a ]
  %t42 = phi i64 [ %t35, %block_0_20248a ]
  ; r41 := (bv_add r37 (0xffffffffffffffff : bv 64))
  %t43 = add i64 %t39, 18446744073709551615
  ; r42 := (div 64 (0x0 : bv 64) r35 r36)
  %t44 = call { i64, i64 } (i64, i64, i64) asm sideeffect "div $4", "={ax},={dx},{dx},{ax},r,~{flags}"(i64 0, i64 %t37, i64 %t38)
  ; r43 := (tuple_field r42 0)
  %t45 = extractvalue { i64, i64 } %t44, 0
  ; r44 := (tuple_field r42 1)
  %t46 = extractvalue { i64, i64 } %t44, 1
  ; r45 := (trunc r44 32)
  %t47 = trunc i64 %t46 to i32
  ; r46 := (bv_add r45 (0x30 : bv 32))
  %t48 = add i32 %t47, 48
  ; r47 := (trunc r46 8)
  %t49 = trunc i32 %t48 to i8
  ; r48 := (uext r46 64)
  %t50 = zext i32 %t48 to i64
  ; r49 := (bv_add r39 r48)
  %t51 = add i64 %t41, %t50
  ; r50 := (trunc r49 32)
  %t52 = trunc i64 %t51 to i32
  ; r51 := (bv_ult (0x39 : bv 8) r47)
  %t53 = icmp ult i8 57, %t49
  ; r52 := (mux r51 r50 r46)
  %t54 = select i1 %t53, i32 %t52, i32 %t48
  ; r53 := (trunc r52 8)
  %t55 = trunc i32 %t54 to i8
  ; write r41 r53
  %t56 = inttoptr i64 %t43 to i8*
  store i8 %t55, i8* %t56
  br label %block_0_2024a7
block_0_2024a7:
  %t57 = phi i64 [ %t12, %block_0_202464 ], [ %t45, %block_0_20248f ]
  %t58 = phi i64 [ %t20, %block_0_202464 ], [ %t38, %block_0_20248f ]
  %t59 = phi i64 [ %t16, %block_0_202464 ], [ %t43, %block_0_20248f ]
  %t60 = phi i64 [ %t14, %block_0_202464 ], [ %t40, %block_0_20248f ]
  %t61 = phi i64 [ %t24, %block_0_202464 ], [ %t41, %block_0_20248f ]
  %t62 = phi i64 [ %t16, %block_0_202464 ], [ %t42, %block_0_20248f ]
  ; r60 := (trunc r59 32)
  %t63 = trunc i64 %t62 to i32
  ; r61 := (trunc r56 32)
  %t64 = trunc i64 %t59 to i32
  ; r62 := (bv_sub r60 r61)
  %t65 = sub i32 %t63, %t64
  ; r63 := (uext r62 64)
  %t66 = zext i32 %t65 to i64
  ; r64 := (bv_ult r57 r56)
  %t67 = icmp ult i64 %t60, %t59
  br i1 %t67, label %block_0_20248a, label %block_0_2024b1
block_0_2024b1:
  %t68 = phi i64 [ 1, %block_0_20247a ], [ %t31, %block_0_20248a ], [ %t66, %block_0_2024a7 ]
  %t69 = phi i64 [ %t27, %block_0_20247a ], [ %t32, %block_0_20248a ], [ %t59, %block_0_2024a7 ]
  %t70 = phi i64 [ %t25, %block_0_20247a ], [ %t33, %block_0_20248a ], [ %t60, %block_0_2024a7 ]
  ; r68 := (bv_add r65 (0x1 : bv 64))
  %t71 = add i64 %t68, 1
  ; r69 := (trunc r68 32)
  %t72 = trunc i64 %t71 to i32
  ; r70 := (uext r69 64)
  %t73 = zext i32 %t72 to i64
  ; call reopt_memmove_0_0x202411(r67, r66, r70)
  call void (i64, i64, i64) @reopt_memmove_0_0x202411(i64 %t70, i64 %t69, i64 %t73)
  br label %block_0_2024b9
block_0_2024b9:
  ret void
}
define void @strcpy(i64 %arg0, i64 %arg1) {
block_0_202858:
  br label %block_0_20285b
block_0_20285b:
  %t0 = phi i64 [ %arg1, %block_0_202858 ], [ %t4, %block_0_20285b ]
  %t1 = phi i64 [ %arg0, %block_0_202858 ], [ %t7, %block_0_20285b ]
  ; r2 := (read r0 (bv 8))
  %t2 = inttoptr i64 %t0 to i8*
  %t3 = load i8, i8* %t2
  ; r3 := (bv_add r0 (0x1 : bv 64))
  %t4 = add i64 %t0, 1
  ; r4 := (eq r2 (0x0 : bv 8))
  %t5 = icmp eq i8 %t3, 0
  ; write r1 r2
  %t6 = inttoptr i64 %t1 to i8*
  store i8 %t3, i8* %t6
  ; r5 := (bv_add r1 (0x1 : bv 64))
  %t7 = add i64 %t1, 1
  br i1 %t5, label %block_0_202861, label %block_0_20285b
block_0_202861:
  ret void
}