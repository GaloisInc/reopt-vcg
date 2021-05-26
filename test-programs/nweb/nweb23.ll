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
declare i64 @close(i64)
declare void @exit(i64)
declare void @logger(i64, i64, i64, i64)
declare i64 @lseek(i64, i64, i64)
declare i64 @open(i64, i64, ...)
declare i64 @read(i64, i64, i64)
declare i64 @sleep(i64)
declare i64 @sprintf(i64, i64, ...)
declare i64 @strcpy(i64, i64)
declare i64 @strlen(i64)
declare i64 @strncmp(i64, i64, i64)
declare i64 @write(i64, i64, i64)
define void @_dl_relocate_static_pie() {
block_0_401200:
  ret void
}
define void @reopt_deregister_tm_clones_0_0x401210() {
block_0_401210:
  br label %block_0_401230
block_0_401230:
  ret void
}
define void @reopt_register_tm_clones_0_0x401240() {
block_0_401240:
  br label %block_0_401270
block_0_401270:
  ret void
}
define void @reopt___do_global_dtors_aux_0_0x401280() {
block_0_401280:
  ; r0 := (read (0x4041c0 : bv 64) (bv 8))
  %t0 = inttoptr i64 4211136 to i8*
  %t1 = load i8, i8* %t0
  ; r1 := (eq r0 (0x0 : bv 8))
  %t2 = icmp eq i8 %t1, 0
  br i1 %t2, label %block_0_40128d, label %block_0_4012a0
block_0_40128d:
  ; call reopt_deregister_tm_clones_0_0x401210()
  call void () @reopt_deregister_tm_clones_0_0x401210()
  br label %block_0_401296
block_0_401296:
  ; write (0x4041c0 : bv 64) (0x1 : bv 8)
  %t3 = inttoptr i64 4211136 to i8*
  store i8 1, i8* %t3
  ret void
block_0_4012a0:
  ret void
}
define void @reopt_frame_dummy_0_0x4012b0() {
block_0_4012b0:
  call void () @reopt_register_tm_clones_0_0x401240()
  ret void
}
define void @web(i64 %arg0, i64 %arg1) {
block_0_4014f0:
  ; r0 := (trunc arg0 32)
  %t0 = trunc i64 %arg0 to i32
  ; r1 := (trunc arg1 32)
  %t1 = trunc i64 %arg1 to i32
  ; r2 := (uext r0 64)
  %t2 = zext i32 %t0 to i64
  ; r3 := call read(r2, (0x4041d0 : bv 64), (0x1fa0 : bv 64))
  %t3 = call i64 (i64, i64, i64) @read(i64 %t2, i64 4211152, i64 8096)
  br label %block_0_401515
block_0_401515:
  %t4 = phi i64 [ %t3, %block_0_4014f0 ]
  %t5 = phi i32 [ %t1, %block_0_4014f0 ]
  %t6 = phi i32 [ %t0, %block_0_4014f0 ]
  ; r7 := (eq r4 (0x0 : bv 64))
  %t7 = icmp eq i64 %t4, 0
  br i1 %t7, label %block_0_40152f, label %block_0_401524
block_0_401524:
  %t8 = phi i64 [ %t4, %block_0_401515 ]
  %t9 = phi i32 [ %t5, %block_0_401515 ]
  %t10 = phi i32 [ %t6, %block_0_401515 ]
  ; r11 := (eq r8 (0xffffffffffffffff : bv 64))
  %t11 = icmp eq i64 %t8, 18446744073709551615
  br i1 %t11, label %block_0_40152f, label %block_0_401550
block_0_40152f:
  %t12 = phi i64 [ %t4, %block_0_401515 ], [ %t8, %block_0_401524 ]
  %t13 = phi i32 [ %t5, %block_0_401515 ], [ %t9, %block_0_401524 ]
  %t14 = phi i32 [ %t6, %block_0_401515 ], [ %t10, %block_0_401524 ]
  ; r15 := (uext r14 64)
  %t15 = zext i32 %t14 to i64
  ; call logger((0x193 : bv 64), (0x4022c4 : bv 64), (0x4023e5 : bv 64), r15)
  call void (i64, i64, i64, i64) @logger(i64 403, i64 4203204, i64 4203493, i64 %t15)
  br label %block_0_401550
block_0_401550:
  %t16 = phi i64 [ %t8, %block_0_401524 ], [ %t12, %block_0_40152f ]
  %t17 = phi i32 [ %t9, %block_0_401524 ], [ %t13, %block_0_40152f ]
  %t18 = phi i32 [ %t10, %block_0_401524 ], [ %t14, %block_0_40152f ]
  ; r19 := (bv_slt r16 (0x0 : bv 64))
  %t19 = icmp slt i64 %t16, 0
  ; r20 := (eq r16 (0x0 : bv 64))
  %t20 = icmp eq i64 %t16, 0
  ; r21 := (or r20 r19)
  %t21 = or i1 %t20, %t19
  br i1 %t21, label %block_0_40157a, label %block_0_40155b
block_0_40155b:
  %t22 = phi i64 [ %t16, %block_0_401550 ]
  %t23 = phi i32 [ %t17, %block_0_401550 ]
  %t24 = phi i32 [ %t18, %block_0_401550 ]
  ; r25 := (ssbb_overflows r22 (0x1fa0 : bv 64) false)
  %t25 = call { i64, i1 } (i64, i64) @llvm.ssub.with.overflow.i64(i64 %t22, i64 8096)
  %t26 = extractvalue { i64, i1 } %t25, 1
  ; r26 := (bv_add r22 (0xffffffffffffe060 : bv 64))
  %t27 = add i64 %t22, 18446744073709543520
  ; r27 := (bv_slt r26 (0x0 : bv 64))
  %t28 = icmp slt i64 %t27, 0
  ; r28 := (eq r27 r25)
  %t29 = icmp eq i1 %t28, %t26
  br i1 %t29, label %block_0_40157a, label %block_0_401569
block_0_401569:
  %t30 = phi i64 [ %t22, %block_0_40155b ]
  %t31 = phi i32 [ %t23, %block_0_40155b ]
  %t32 = phi i32 [ %t24, %block_0_40155b ]
  ; r32 := (bv_add r29 (0x4041d0 : bv 64))
  %t33 = add i64 %t30, 4211152
  ; write r32 (0x0 : bv 8)
  %t34 = inttoptr i64 %t33 to i8*
  store i8 0, i8* %t34
  br label %block_0_401582
block_0_40157a:
  %t35 = phi i64 [ %t16, %block_0_401550 ], [ %t22, %block_0_40155b ]
  %t36 = phi i32 [ %t17, %block_0_401550 ], [ %t23, %block_0_40155b ]
  %t37 = phi i32 [ %t18, %block_0_401550 ], [ %t24, %block_0_40155b ]
  ; write (0x4041d0 : bv 64) (0x0 : bv 8)
  %t38 = inttoptr i64 4211152 to i8*
  store i8 0, i8* %t38
  br label %block_0_401582
block_0_401582:
  %t39 = phi i64 [ %t30, %block_0_401569 ], [ %t35, %block_0_40157a ]
  %t40 = phi i32 [ %t31, %block_0_401569 ], [ %t36, %block_0_40157a ]
  %t41 = phi i32 [ %t32, %block_0_401569 ], [ %t37, %block_0_40157a ]
  br label %block_0_40158a
block_0_40158a:
  %t42 = phi i64 [ %t39, %block_0_401582 ], [ %t75, %block_0_4015ce ]
  %t43 = phi i64 [ 0, %block_0_401582 ], [ %t79, %block_0_4015ce ]
  %t44 = phi i32 [ %t40, %block_0_401582 ], [ %t77, %block_0_4015ce ]
  %t45 = phi i32 [ %t41, %block_0_401582 ], [ %t78, %block_0_4015ce ]
  ; r43 := (ssbb_overflows r40 r39 false)
  %t46 = call { i64, i1 } (i64, i64) @llvm.ssub.with.overflow.i64(i64 %t43, i64 %t42)
  %t47 = extractvalue { i64, i1 } %t46, 1
  ; r44 := (bv_sub r40 r39)
  %t48 = sub i64 %t43, %t42
  ; r45 := (bv_slt r44 (0x0 : bv 64))
  %t49 = icmp slt i64 %t48, 0
  ; r46 := (eq r45 r43)
  %t50 = icmp eq i1 %t49, %t47
  br i1 %t50, label %block_0_4015e4, label %block_0_401598
block_0_401598:
  %t51 = phi i64 [ %t42, %block_0_40158a ]
  %t52 = phi i64 [ %t43, %block_0_40158a ]
  %t53 = phi i32 [ %t44, %block_0_40158a ]
  %t54 = phi i32 [ %t45, %block_0_40158a ]
  ; r51 := (bv_add r48 (0x4041d0 : bv 64))
  %t55 = add i64 %t52, 4211152
  ; r52 := (read r51 (bv 8))
  %t56 = inttoptr i64 %t55 to i8*
  %t57 = load i8, i8* %t56
  ; r53 := (sext r52 32)
  %t58 = sext i8 %t57 to i32
  ; r54 := (eq r53 (0xd : bv 32))
  %t59 = icmp eq i32 %t58, 13
  br i1 %t59, label %block_0_4015c2, label %block_0_4015ad
block_0_4015ad:
  %t60 = phi i64 [ %t51, %block_0_401598 ]
  %t61 = phi i64 [ %t52, %block_0_401598 ]
  %t62 = phi i32 [ %t53, %block_0_401598 ]
  %t63 = phi i32 [ %t54, %block_0_401598 ]
  ; r59 := (bv_add r56 (0x4041d0 : bv 64))
  %t64 = add i64 %t61, 4211152
  ; r60 := (read r59 (bv 8))
  %t65 = inttoptr i64 %t64 to i8*
  %t66 = load i8, i8* %t65
  ; r61 := (sext r60 32)
  %t67 = sext i8 %t66 to i32
  ; r62 := (eq r61 (0xa : bv 32))
  %t68 = icmp eq i32 %t67, 10
  br i1 %t68, label %block_0_4015c2, label %block_0_4015ce
block_0_4015c2:
  %t69 = phi i64 [ %t51, %block_0_401598 ], [ %t60, %block_0_4015ad ]
  %t70 = phi i64 [ %t52, %block_0_401598 ], [ %t61, %block_0_4015ad ]
  %t71 = phi i32 [ %t53, %block_0_401598 ], [ %t62, %block_0_4015ad ]
  %t72 = phi i32 [ %t54, %block_0_401598 ], [ %t63, %block_0_4015ad ]
  ; r67 := (bv_add r64 (0x4041d0 : bv 64))
  %t73 = add i64 %t70, 4211152
  ; write r67 (0x2a : bv 8)
  %t74 = inttoptr i64 %t73 to i8*
  store i8 42, i8* %t74
  br label %block_0_4015ce
block_0_4015ce:
  %t75 = phi i64 [ %t60, %block_0_4015ad ], [ %t69, %block_0_4015c2 ]
  %t76 = phi i64 [ %t61, %block_0_4015ad ], [ %t70, %block_0_4015c2 ]
  %t77 = phi i32 [ %t62, %block_0_4015ad ], [ %t71, %block_0_4015c2 ]
  %t78 = phi i32 [ %t63, %block_0_4015ad ], [ %t72, %block_0_4015c2 ]
  ; r72 := (bv_add r69 (0x1 : bv 64))
  %t79 = add i64 %t76, 1
  br label %block_0_40158a
block_0_4015e4:
  %t80 = phi i32 [ %t44, %block_0_40158a ]
  %t81 = phi i32 [ %t45, %block_0_40158a ]
  ; r75 := (uext r73 64)
  %t82 = zext i32 %t80 to i64
  ; call logger((0x2c : bv 64), (0x4022db : bv 64), (0x4041d0 : bv 64), r75)
  call void (i64, i64, i64, i64) @logger(i64 44, i64 4203227, i64 4211152, i64 %t82)
  br label %block_0_401605
block_0_401605:
  %t83 = phi i32 [ %t80, %block_0_4015e4 ]
  %t84 = phi i32 [ %t81, %block_0_4015e4 ]
  ; r78 := call strncmp((0x4041d0 : bv 64), (0x4022e3 : bv 64), (0x4 : bv 64))
  %t85 = call i64 (i64, i64, i64) @strncmp(i64 4211152, i64 4203235, i64 4)
  br label %block_0_401623
block_0_401623:
  %t86 = phi i64 [ %t85, %block_0_401605 ]
  %t87 = phi i32 [ %t83, %block_0_401605 ]
  %t88 = phi i32 [ %t84, %block_0_401605 ]
  ; r82 := (trunc r79 32)
  %t89 = trunc i64 %t86 to i32
  ; r83 := (eq r82 (0x0 : bv 32))
  %t90 = icmp eq i32 %t89, 0
  br i1 %t90, label %block_0_401674, label %block_0_40162c
block_0_40162c:
  %t91 = phi i32 [ %t87, %block_0_401623 ]
  %t92 = phi i32 [ %t88, %block_0_401623 ]
  ; r86 := call strncmp((0x4041d0 : bv 64), (0x4022e8 : bv 64), (0x4 : bv 64))
  %t93 = call i64 (i64, i64, i64) @strncmp(i64 4211152, i64 4203240, i64 4)
  br label %block_0_40164a
block_0_40164a:
  %t94 = phi i64 [ %t93, %block_0_40162c ]
  %t95 = phi i32 [ %t91, %block_0_40162c ]
  %t96 = phi i32 [ %t92, %block_0_40162c ]
  ; r90 := (trunc r87 32)
  %t97 = trunc i64 %t94 to i32
  ; r91 := (eq r90 (0x0 : bv 32))
  %t98 = icmp eq i32 %t97, 0
  br i1 %t98, label %block_0_401674, label %block_0_401653
block_0_401653:
  %t99 = phi i32 [ %t95, %block_0_40164a ]
  %t100 = phi i32 [ %t96, %block_0_40164a ]
  ; r94 := (uext r93 64)
  %t101 = zext i32 %t100 to i64
  ; call logger((0x193 : bv 64), (0x4022ed : bv 64), (0x4041d0 : bv 64), r94)
  call void (i64, i64, i64, i64) @logger(i64 403, i64 4203245, i64 4211152, i64 %t101)
  br label %block_0_401674
block_0_401674:
  %t102 = phi i32 [ %t87, %block_0_401623 ], [ %t95, %block_0_40164a ], [ %t99, %block_0_401653 ]
  %t103 = phi i32 [ %t88, %block_0_401623 ], [ %t96, %block_0_40164a ], [ %t100, %block_0_401653 ]
  br label %block_0_40167c
block_0_40167c:
  %t104 = phi i64 [ 4, %block_0_401674 ], [ %t128, %block_0_4016b0 ]
  %t105 = phi i32 [ %t102, %block_0_401674 ], [ %t126, %block_0_4016b0 ]
  %t106 = phi i32 [ %t103, %block_0_401674 ], [ %t127, %block_0_4016b0 ]
  ; r100 := (ssbb_overflows r97 (0x1fa0 : bv 64) false)
  %t107 = call { i64, i1 } (i64, i64) @llvm.ssub.with.overflow.i64(i64 %t104, i64 8096)
  %t108 = extractvalue { i64, i1 } %t107, 1
  ; r101 := (bv_add r97 (0xffffffffffffe060 : bv 64))
  %t109 = add i64 %t104, 18446744073709543520
  ; r102 := (bv_slt r101 (0x0 : bv 64))
  %t110 = icmp slt i64 %t109, 0
  ; r103 := (eq r102 r100)
  %t111 = icmp eq i1 %t110, %t108
  br i1 %t111, label %block_0_4016c6, label %block_0_40168a
block_0_40168a:
  %t112 = phi i64 [ %t104, %block_0_40167c ]
  %t113 = phi i32 [ %t105, %block_0_40167c ]
  %t114 = phi i32 [ %t106, %block_0_40167c ]
  ; r107 := (bv_add r104 (0x4041d0 : bv 64))
  %t115 = add i64 %t112, 4211152
  ; r108 := (read r107 (bv 8))
  %t116 = inttoptr i64 %t115 to i8*
  %t117 = load i8, i8* %t116
  ; r109 := (sext r108 32)
  %t118 = sext i8 %t117 to i32
  ; r110 := (eq r109 (0x20 : bv 32))
  %t119 = icmp eq i32 %t118, 32
  br i1 %t119, label %block_0_40169f, label %block_0_4016b0
block_0_40169f:
  %t120 = phi i64 [ %t112, %block_0_40168a ]
  %t121 = phi i32 [ %t113, %block_0_40168a ]
  %t122 = phi i32 [ %t114, %block_0_40168a ]
  ; r114 := (bv_add r111 (0x4041d0 : bv 64))
  %t123 = add i64 %t120, 4211152
  ; write r114 (0x0 : bv 8)
  %t124 = inttoptr i64 %t123 to i8*
  store i8 0, i8* %t124
  br label %block_0_4016c6
block_0_4016b0:
  %t125 = phi i64 [ %t112, %block_0_40168a ]
  %t126 = phi i32 [ %t113, %block_0_40168a ]
  %t127 = phi i32 [ %t114, %block_0_40168a ]
  ; r118 := (bv_add r115 (0x1 : bv 64))
  %t128 = add i64 %t125, 1
  br label %block_0_40167c
block_0_4016c6:
  %t129 = phi i64 [ %t104, %block_0_40167c ], [ %t120, %block_0_40169f ]
  %t130 = phi i32 [ %t105, %block_0_40167c ], [ %t121, %block_0_40169f ]
  %t131 = phi i32 [ %t106, %block_0_40167c ], [ %t122, %block_0_40169f ]
  br label %block_0_4016cd
block_0_4016cd:
  %t132 = phi i64 [ %t129, %block_0_4016c6 ], [ %t169, %block_0_401731 ]
  %t133 = phi i32 [ 0, %block_0_4016c6 ], [ %t173, %block_0_401731 ]
  %t134 = phi i32 [ %t130, %block_0_4016c6 ], [ %t171, %block_0_401731 ]
  %t135 = phi i32 [ %t131, %block_0_4016c6 ], [ %t172, %block_0_401731 ]
  ; r126 := (sext r123 64)
  %t136 = sext i32 %t133 to i64
  ; r127 := (bv_add r122 (0xffffffffffffffff : bv 64))
  %t137 = add i64 %t132, 18446744073709551615
  ; r128 := (ssbb_overflows r126 r127 false)
  %t138 = call { i64, i1 } (i64, i64) @llvm.ssub.with.overflow.i64(i64 %t136, i64 %t137)
  %t139 = extractvalue { i64, i1 } %t138, 1
  ; r129 := (bv_sub r126 r127)
  %t140 = sub i64 %t136, %t137
  ; r130 := (bv_slt r129 (0x0 : bv 64))
  %t141 = icmp slt i64 %t140, 0
  ; r131 := (eq r130 r128)
  %t142 = icmp eq i1 %t141, %t139
  br i1 %t142, label %block_0_401744, label %block_0_4016e2
block_0_4016e2:
  %t143 = phi i64 [ %t132, %block_0_4016cd ]
  %t144 = phi i32 [ %t133, %block_0_4016cd ]
  %t145 = phi i32 [ %t134, %block_0_4016cd ]
  %t146 = phi i32 [ %t135, %block_0_4016cd ]
  ; r136 := (sext r133 64)
  %t147 = sext i32 %t144 to i64
  ; r137 := (bv_add r136 (0x4041d0 : bv 64))
  %t148 = add i64 %t147, 4211152
  ; r138 := (read r137 (bv 8))
  %t149 = inttoptr i64 %t148 to i8*
  %t150 = load i8, i8* %t149
  ; r139 := (sext r138 32)
  %t151 = sext i8 %t150 to i32
  ; r140 := (eq r139 (0x2e : bv 32))
  %t152 = icmp eq i32 %t151, 46
  br i1 %t152, label %block_0_4016f7, label %block_0_401731
block_0_4016f7:
  %t153 = phi i64 [ %t143, %block_0_4016e2 ]
  %t154 = phi i32 [ %t144, %block_0_4016e2 ]
  %t155 = phi i32 [ %t145, %block_0_4016e2 ]
  %t156 = phi i32 [ %t146, %block_0_4016e2 ]
  ; r145 := (bv_add r142 (0x1 : bv 32))
  %t157 = add i32 %t154, 1
  ; r146 := (sext r145 64)
  %t158 = sext i32 %t157 to i64
  ; r147 := (bv_add r146 (0x4041d0 : bv 64))
  %t159 = add i64 %t158, 4211152
  ; r148 := (read r147 (bv 8))
  %t160 = inttoptr i64 %t159 to i8*
  %t161 = load i8, i8* %t160
  ; r149 := (sext r148 32)
  %t162 = sext i8 %t161 to i32
  ; r150 := (eq r149 (0x2e : bv 32))
  %t163 = icmp eq i32 %t162, 46
  br i1 %t163, label %block_0_401710, label %block_0_401731
block_0_401710:
  %t164 = phi i64 [ %t153, %block_0_4016f7 ]
  %t165 = phi i32 [ %t154, %block_0_4016f7 ]
  %t166 = phi i32 [ %t155, %block_0_4016f7 ]
  %t167 = phi i32 [ %t156, %block_0_4016f7 ]
  ; r155 := (uext r154 64)
  %t168 = zext i32 %t167 to i64
  ; call logger((0x193 : bv 64), (0x402311 : bv 64), (0x4041d0 : bv 64), r155)
  call void (i64, i64, i64, i64) @logger(i64 403, i64 4203281, i64 4211152, i64 %t168)
  br label %block_0_401731
block_0_401731:
  %t169 = phi i64 [ %t143, %block_0_4016e2 ], [ %t153, %block_0_4016f7 ], [ %t164, %block_0_401710 ]
  %t170 = phi i32 [ %t144, %block_0_4016e2 ], [ %t154, %block_0_4016f7 ], [ %t165, %block_0_401710 ]
  %t171 = phi i32 [ %t145, %block_0_4016e2 ], [ %t155, %block_0_4016f7 ], [ %t166, %block_0_401710 ]
  %t172 = phi i32 [ %t146, %block_0_4016e2 ], [ %t156, %block_0_4016f7 ], [ %t167, %block_0_401710 ]
  ; r160 := (bv_add r157 (0x1 : bv 32))
  %t173 = add i32 %t170, 1
  br label %block_0_4016cd
block_0_401744:
  %t174 = phi i32 [ %t134, %block_0_4016cd ]
  %t175 = phi i32 [ %t135, %block_0_4016cd ]
  ; r163 := call strncmp((0x4041d0 : bv 64), (0x4026c7 : bv 64), (0x6 : bv 64))
  %t176 = call i64 (i64, i64, i64) @strncmp(i64 4211152, i64 4204231, i64 6)
  br label %block_0_401762
block_0_401762:
  %t177 = phi i64 [ %t176, %block_0_401744 ]
  %t178 = phi i32 [ %t174, %block_0_401744 ]
  %t179 = phi i32 [ %t175, %block_0_401744 ]
  ; r167 := (trunc r164 32)
  %t180 = trunc i64 %t177 to i32
  ; r168 := (eq r167 (0x0 : bv 32))
  %t181 = icmp eq i32 %t180, 0
  br i1 %t181, label %block_0_401792, label %block_0_40176b
block_0_40176b:
  %t182 = phi i32 [ %t178, %block_0_401762 ]
  %t183 = phi i32 [ %t179, %block_0_401762 ]
  ; r171 := call strncmp((0x4041d0 : bv 64), (0x4026ce : bv 64), (0x6 : bv 64))
  %t184 = call i64 (i64, i64, i64) @strncmp(i64 4211152, i64 4204238, i64 6)
  br label %block_0_401789
block_0_401789:
  %t185 = phi i64 [ %t184, %block_0_40176b ]
  %t186 = phi i32 [ %t182, %block_0_40176b ]
  %t187 = phi i32 [ %t183, %block_0_40176b ]
  ; r175 := (trunc r172 32)
  %t188 = trunc i64 %t185 to i32
  ; r176 := (eq r175 (0x0 : bv 32))
  %t189 = icmp eq i32 %t188, 0
  br i1 %t189, label %block_0_401792, label %block_0_4017a1
block_0_401792:
  %t190 = phi i32 [ %t178, %block_0_401762 ], [ %t186, %block_0_401789 ]
  %t191 = phi i32 [ %t179, %block_0_401762 ], [ %t187, %block_0_401789 ]
  ; r179 := call strcpy((0x4041d0 : bv 64), (0x402340 : bv 64))
  %t192 = call i64 (i64, i64) @strcpy(i64 4211152, i64 4203328)
  br label %block_0_4017a1
block_0_4017a1:
  %t193 = phi i32 [ %t186, %block_0_401789 ], [ %t190, %block_0_401792 ]
  %t194 = phi i32 [ %t187, %block_0_401789 ], [ %t191, %block_0_401792 ]
  ; r182 := call strlen((0x4041d0 : bv 64))
  %t195 = call i64 (i64) @strlen(i64 4211152)
  br label %block_0_4017ab
block_0_4017ab:
  %t196 = phi i64 [ %t195, %block_0_4017a1 ]
  %t197 = phi i32 [ %t193, %block_0_4017a1 ]
  %t198 = phi i32 [ %t194, %block_0_4017a1 ]
  ; r186 := (trunc r183 32)
  %t199 = trunc i64 %t196 to i32
  br label %block_0_4017be
block_0_4017be:
  %t200 = phi i64 [ 0, %block_0_4017ab ], [ %t249, %block_0_40185f ]
  %t201 = phi i64 [ 0, %block_0_4017ab ], [ %t254, %block_0_40185f ]
  %t202 = phi i32 [ %t199, %block_0_4017ab ], [ %t251, %block_0_40185f ]
  %t203 = phi i32 [ %t197, %block_0_4017ab ], [ %t252, %block_0_40185f ]
  %t204 = phi i32 [ %t198, %block_0_4017ab ], [ %t253, %block_0_40185f ]
  ; r192 := (bv_shl r188 (0x4 : bv 64))
  %t205 = shl i64 %t201, 4
  ; r193 := (bv_add r192 (0x404100 : bv 64))
  %t206 = add i64 %t205, 4210944
  ; r194 := (read r193 (bv 64))
  %t207 = inttoptr i64 %t206 to i64*
  %t208 = load i64, i64* %t207
  ; r195 := (eq r194 (0x0 : bv 64))
  %t209 = icmp eq i64 %t208, 0
  br i1 %t209, label %block_0_401875, label %block_0_4017dd
block_0_4017dd:
  %t210 = phi i64 [ %t200, %block_0_4017be ]
  %t211 = phi i64 [ %t201, %block_0_4017be ]
  %t212 = phi i32 [ %t202, %block_0_4017be ]
  %t213 = phi i32 [ %t203, %block_0_4017be ]
  %t214 = phi i32 [ %t204, %block_0_4017be ]
  ; r201 := (bv_shl r197 (0x4 : bv 64))
  %t215 = shl i64 %t211, 4
  ; r202 := (bv_add r201 (0x404100 : bv 64))
  %t216 = add i64 %t215, 4210944
  ; r203 := (read r202 (bv 64))
  %t217 = inttoptr i64 %t216 to i64*
  %t218 = load i64, i64* %t217
  ; r204 := call strlen(r203)
  %t219 = call i64 (i64) @strlen(i64 %t218)
  br label %block_0_4017fa
block_0_4017fa:
  %t220 = phi i64 [ %t219, %block_0_4017dd ]
  %t221 = phi i64 [ %t210, %block_0_4017dd ]
  %t222 = phi i64 [ %t211, %block_0_4017dd ]
  %t223 = phi i32 [ %t212, %block_0_4017dd ]
  %t224 = phi i32 [ %t213, %block_0_4017dd ]
  %t225 = phi i32 [ %t214, %block_0_4017dd ]
  ; r211 := (sext r208 64)
  %t226 = sext i32 %t223 to i64
  ; r212 := (bv_sub r211 r205)
  %t227 = sub i64 %t226, %t220
  ; r213 := (bv_add r212 (0x4041d0 : bv 64))
  %t228 = add i64 %t227, 4211152
  ; r214 := (bv_shl r207 (0x4 : bv 64))
  %t229 = shl i64 %t222, 4
  ; r215 := (bv_add r214 (0x404100 : bv 64))
  %t230 = add i64 %t229, 4210944
  ; r216 := (read r215 (bv 64))
  %t231 = inttoptr i64 %t230 to i64*
  %t232 = load i64, i64* %t231
  ; r217 := call strncmp(r213, r216, r205)
  %t233 = call i64 (i64, i64, i64) @strncmp(i64 %t228, i64 %t232, i64 %t220)
  br label %block_0_401834
block_0_401834:
  %t234 = phi i64 [ %t233, %block_0_4017fa ]
  %t235 = phi i64 [ %t221, %block_0_4017fa ]
  %t236 = phi i64 [ %t222, %block_0_4017fa ]
  %t237 = phi i32 [ %t223, %block_0_4017fa ]
  %t238 = phi i32 [ %t224, %block_0_4017fa ]
  %t239 = phi i32 [ %t225, %block_0_4017fa ]
  ; r224 := (trunc r218 32)
  %t240 = trunc i64 %t234 to i32
  ; r225 := (eq r224 (0x0 : bv 32))
  %t241 = icmp eq i32 %t240, 0
  br i1 %t241, label %block_0_40183d, label %block_0_40185f
block_0_40183d:
  %t242 = phi i64 [ %t236, %block_0_401834 ]
  %t243 = phi i32 [ %t238, %block_0_401834 ]
  %t244 = phi i32 [ %t239, %block_0_401834 ]
  ; r229 := (bv_shl r226 (0x4 : bv 64))
  %t245 = shl i64 %t242, 4
  ; r230 := (bv_add r229 (0x404108 : bv 64))
  %t246 = add i64 %t245, 4210952
  ; r231 := (read r230 (bv 64))
  %t247 = inttoptr i64 %t246 to i64*
  %t248 = load i64, i64* %t247
  br label %block_0_401875
block_0_40185f:
  %t249 = phi i64 [ %t235, %block_0_401834 ]
  %t250 = phi i64 [ %t236, %block_0_401834 ]
  %t251 = phi i32 [ %t237, %block_0_401834 ]
  %t252 = phi i32 [ %t238, %block_0_401834 ]
  %t253 = phi i32 [ %t239, %block_0_401834 ]
  ; r237 := (bv_add r233 (0x1 : bv 64))
  %t254 = add i64 %t250, 1
  br label %block_0_4017be
block_0_401875:
  %t255 = phi i64 [ %t200, %block_0_4017be ], [ %t248, %block_0_40183d ]
  %t256 = phi i32 [ %t203, %block_0_4017be ], [ %t243, %block_0_40183d ]
  %t257 = phi i32 [ %t204, %block_0_4017be ], [ %t244, %block_0_40183d ]
  ; r241 := (eq r238 (0x0 : bv 64))
  %t258 = icmp eq i64 %t255, 0
  br i1 %t258, label %block_0_401880, label %block_0_4018a1
block_0_401880:
  %t259 = phi i64 [ %t255, %block_0_401875 ]
  %t260 = phi i32 [ %t256, %block_0_401875 ]
  %t261 = phi i32 [ %t257, %block_0_401875 ]
  ; r245 := (uext r244 64)
  %t262 = zext i32 %t261 to i64
  ; call logger((0x193 : bv 64), (0x402350 : bv 64), (0x4041d0 : bv 64), r245)
  call void (i64, i64, i64, i64) @logger(i64 403, i64 4203344, i64 4211152, i64 %t262)
  br label %block_0_4018a1
block_0_4018a1:
  %t263 = phi i64 [ %t255, %block_0_401875 ], [ %t259, %block_0_401880 ]
  %t264 = phi i32 [ %t256, %block_0_401875 ], [ %t260, %block_0_401880 ]
  %t265 = phi i32 [ %t257, %block_0_401875 ], [ %t261, %block_0_401880 ]
  ; r249 := call open((0x4041d5 : bv 64), (0x0 : bv 64))
  %t266 = call i64 (i64, i64, ...) @open(i64 4211157, i64 0)
  br label %block_0_4018b8
block_0_4018b8:
  %t267 = phi i64 [ %t266, %block_0_4018a1 ]
  %t268 = phi i64 [ %t263, %block_0_4018a1 ]
  %t269 = phi i32 [ %t264, %block_0_4018a1 ]
  %t270 = phi i32 [ %t265, %block_0_4018a1 ]
  ; r254 := (trunc r250 32)
  %t271 = trunc i64 %t267 to i32
  ; r255 := (eq r254 (0xffffffff : bv 32))
  %t272 = icmp eq i32 %t271, 4294967295
  br i1 %t272, label %block_0_4018c4, label %block_0_4018e9
block_0_4018c4:
  %t273 = phi i64 [ %t268, %block_0_4018b8 ]
  %t274 = phi i32 [ %t271, %block_0_4018b8 ]
  %t275 = phi i32 [ %t269, %block_0_4018b8 ]
  %t276 = phi i32 [ %t270, %block_0_4018b8 ]
  ; r260 := (uext r259 64)
  %t277 = zext i32 %t276 to i64
  ; call logger((0x194 : bv 64), (0x402372 : bv 64), (0x4041d5 : bv 64), r260)
  call void (i64, i64, i64, i64) @logger(i64 404, i64 4203378, i64 4211157, i64 %t277)
  br label %block_0_4018e9
block_0_4018e9:
  %t278 = phi i64 [ %t268, %block_0_4018b8 ], [ %t273, %block_0_4018c4 ]
  %t279 = phi i32 [ %t271, %block_0_4018b8 ], [ %t274, %block_0_4018c4 ]
  %t280 = phi i32 [ %t269, %block_0_4018b8 ], [ %t275, %block_0_4018c4 ]
  %t281 = phi i32 [ %t270, %block_0_4018b8 ], [ %t276, %block_0_4018c4 ]
  ; r265 := (uext r263 64)
  %t282 = zext i32 %t280 to i64
  ; call logger((0x2c : bv 64), (0x402386 : bv 64), (0x4041d5 : bv 64), r265)
  call void (i64, i64, i64, i64) @logger(i64 44, i64 4203398, i64 4211157, i64 %t282)
  br label %block_0_40190e
block_0_40190e:
  %t283 = phi i64 [ %t278, %block_0_4018e9 ]
  %t284 = phi i32 [ %t279, %block_0_4018e9 ]
  %t285 = phi i32 [ %t280, %block_0_4018e9 ]
  %t286 = phi i32 [ %t281, %block_0_4018e9 ]
  ; r270 := (uext r267 64)
  %t287 = zext i32 %t284 to i64
  ; r271 := call lseek(r270, (0x0 : bv 64), (0x2 : bv 64))
  %t288 = call i64 (i64, i64, i64) @lseek(i64 %t287, i64 0, i64 2)
  br label %block_0_40191f
block_0_40191f:
  %t289 = phi i64 [ %t288, %block_0_40190e ]
  %t290 = phi i64 [ %t283, %block_0_40190e ]
  %t291 = phi i32 [ %t284, %block_0_40190e ]
  %t292 = phi i32 [ %t285, %block_0_40190e ]
  %t293 = phi i32 [ %t286, %block_0_40190e ]
  ; r277 := (uext r274 64)
  %t294 = zext i32 %t291 to i64
  ; r278 := call lseek(r277, (0x0 : bv 64), (0x0 : bv 64))
  %t295 = call i64 (i64, i64, i64) @lseek(i64 %t294, i64 0, i64 0)
  br label %block_0_401931
block_0_401931:
  %t296 = phi i64 [ %t290, %block_0_40191f ]
  %t297 = phi i64 [ %t289, %block_0_40191f ]
  %t298 = phi i32 [ %t291, %block_0_40191f ]
  %t299 = phi i32 [ %t292, %block_0_40191f ]
  %t300 = phi i32 [ %t293, %block_0_40191f ]
  ; r284 := call sprintf((0x4041d0 : bv 64), (0x40238b : bv 64), (0x17 : bv 64), r280, r279)
  %t301 = call i64 (i64, i64, ...) @sprintf(i64 4211152, i64 4203403, i64 23, i64 %t297, i64 %t296)
  br label %block_0_401959
block_0_401959:
  %t302 = phi i32 [ %t298, %block_0_401931 ]
  %t303 = phi i32 [ %t299, %block_0_401931 ]
  %t304 = phi i32 [ %t300, %block_0_401931 ]
  ; r288 := (uext r286 64)
  %t305 = zext i32 %t303 to i64
  ; call logger((0x2c : bv 64), (0x4023e6 : bv 64), (0x4041d0 : bv 64), r288)
  call void (i64, i64, i64, i64) @logger(i64 44, i64 4203494, i64 4211152, i64 %t305)
  br label %block_0_40197a
block_0_40197a:
  %t306 = phi i32 [ %t302, %block_0_401959 ]
  %t307 = phi i32 [ %t304, %block_0_401959 ]
  ; r291 := call strlen((0x4041d0 : bv 64))
  %t308 = call i64 (i64) @strlen(i64 4211152)
  br label %block_0_40198a
block_0_40198a:
  %t309 = phi i64 [ %t308, %block_0_40197a ]
  %t310 = phi i32 [ %t307, %block_0_40197a ]
  %t311 = phi i32 [ %t306, %block_0_40197a ]
  %t312 = phi i32 [ %t307, %block_0_40197a ]
  ; r296 := (uext r293 64)
  %t313 = zext i32 %t310 to i64
  ; r297 := call write(r296, (0x4041d0 : bv 64), r292)
  %t314 = call i64 (i64, i64, i64) @write(i64 %t313, i64 4211152, i64 %t309)
  br label %block_0_40199f
block_0_40199f:
  %t315 = phi i32 [ %t311, %block_0_40198a ], [ %t330, %block_0_4019da ]
  %t316 = phi i32 [ %t312, %block_0_40198a ], [ %t331, %block_0_4019da ]
  ; r300 := (uext r298 64)
  %t317 = zext i32 %t315 to i64
  ; r301 := call read(r300, (0x4041d0 : bv 64), (0x1fa0 : bv 64))
  %t318 = call i64 (i64, i64, i64) @read(i64 %t317, i64 4211152, i64 8096)
  br label %block_0_4019b6
block_0_4019b6:
  %t319 = phi i64 [ %t318, %block_0_40199f ]
  %t320 = phi i32 [ %t315, %block_0_40199f ]
  %t321 = phi i32 [ %t316, %block_0_40199f ]
  ; r305 := (bv_slt r302 (0x0 : bv 64))
  %t322 = icmp slt i64 %t319, 0
  ; r306 := (eq r302 (0x0 : bv 64))
  %t323 = icmp eq i64 %t319, 0
  ; r307 := (or r306 r305)
  %t324 = or i1 %t323, %t322
  br i1 %t324, label %block_0_4019df, label %block_0_4019c4
block_0_4019c4:
  %t325 = phi i64 [ %t319, %block_0_4019b6 ]
  %t326 = phi i32 [ %t320, %block_0_4019b6 ]
  %t327 = phi i32 [ %t321, %block_0_4019b6 ]
  ; r311 := (uext r310 64)
  %t328 = zext i32 %t327 to i64
  ; r312 := call write(r311, (0x4041d0 : bv 64), r308)
  %t329 = call i64 (i64, i64, i64) @write(i64 %t328, i64 4211152, i64 %t325)
  br label %block_0_4019da
block_0_4019da:
  %t330 = phi i32 [ %t326, %block_0_4019c4 ]
  %t331 = phi i32 [ %t327, %block_0_4019c4 ]
  br label %block_0_40199f
block_0_4019df:
  %t332 = phi i32 [ %t321, %block_0_4019b6 ]
  ; r316 := call sleep((0x1 : bv 64))
  %t333 = call i64 (i64) @sleep(i64 1)
  br label %block_0_4019e9
block_0_4019e9:
  %t334 = phi i32 [ %t332, %block_0_4019df ]
  ; r318 := (uext r317 64)
  %t335 = zext i32 %t334 to i64
  ; r319 := call close(r318)
  %t336 = call i64 (i64) @close(i64 %t335)
  br label %block_0_4019f1
block_0_4019f1:
  call void (i64) @exit(i64 1)
  ret void
}
define void @__libc_csu_fini() {
block_0_401f40:
  ret void
}
define void @_fini() {
block_0_401f48:
  ret void
}