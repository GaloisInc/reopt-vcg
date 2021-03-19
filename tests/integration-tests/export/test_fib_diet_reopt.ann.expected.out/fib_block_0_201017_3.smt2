; fib.block_0_201017.0 @ 0x20101f: direction flag is expected value (jump)
(set-logic ALL)
(set-option :produce-models true)
(define-fun mem_readbv8 ((arg (Array (_ BitVec 64) (_ BitVec 8))) (arg0 (_ BitVec 64))) (_ BitVec 8) (select arg (bvadd arg0 #x0000000000000000)))
(define-fun mem_writebv8 ((arg1 (Array (_ BitVec 64) (_ BitVec 8))) (arg2 (_ BitVec 64)) (arg3 (_ BitVec 8))) (Array (_ BitVec 64) (_ BitVec 8)) (store arg1 arg2 ((_ extract 7 0) arg3)))
(define-fun mem_readbv16 ((arg4 (Array (_ BitVec 64) (_ BitVec 8))) (arg5 (_ BitVec 64))) (_ BitVec 16) (concat (select arg4 (bvadd arg5 #x0000000000000001)) (select arg4 (bvadd arg5 #x0000000000000000))))
(define-fun mem_writebv16 ((arg6 (Array (_ BitVec 64) (_ BitVec 8))) (arg7 (_ BitVec 64)) (arg8 (_ BitVec 16))) (Array (_ BitVec 64) (_ BitVec 8)) (store (store arg6 arg7 ((_ extract 7 0) arg8)) (bvadd arg7 #x0000000000000001) ((_ extract 15 8) arg8)))
(define-fun mem_readbv32 ((arg9 (Array (_ BitVec 64) (_ BitVec 8))) (arg10 (_ BitVec 64))) (_ BitVec 32) (concat (concat (concat (select arg9 (bvadd arg10 #x0000000000000003)) (select arg9 (bvadd arg10 #x0000000000000002))) (select arg9 (bvadd arg10 #x0000000000000001))) (select arg9 (bvadd arg10 #x0000000000000000))))
(define-fun mem_writebv32 ((arg11 (Array (_ BitVec 64) (_ BitVec 8))) (arg12 (_ BitVec 64)) (arg13 (_ BitVec 32))) (Array (_ BitVec 64) (_ BitVec 8)) (store (store (store (store arg11 arg12 ((_ extract 7 0) arg13)) (bvadd arg12 #x0000000000000001) ((_ extract 15 8) arg13)) (bvadd (bvadd arg12 #x0000000000000001) #x0000000000000001) ((_ extract 23 16) arg13)) (bvadd (bvadd (bvadd arg12 #x0000000000000001) #x0000000000000001) #x0000000000000001) ((_ extract 31 24) arg13)))
(define-fun mem_readbv64 ((arg14 (Array (_ BitVec 64) (_ BitVec 8))) (arg15 (_ BitVec 64))) (_ BitVec 64) (concat (concat (concat (concat (concat (concat (concat (select arg14 (bvadd arg15 #x0000000000000007)) (select arg14 (bvadd arg15 #x0000000000000006))) (select arg14 (bvadd arg15 #x0000000000000005))) (select arg14 (bvadd arg15 #x0000000000000004))) (select arg14 (bvadd arg15 #x0000000000000003))) (select arg14 (bvadd arg15 #x0000000000000002))) (select arg14 (bvadd arg15 #x0000000000000001))) (select arg14 (bvadd arg15 #x0000000000000000))))
(define-fun mem_writebv64 ((arg16 (Array (_ BitVec 64) (_ BitVec 8))) (arg17 (_ BitVec 64)) (arg18 (_ BitVec 64))) (Array (_ BitVec 64) (_ BitVec 8)) (store (store (store (store (store (store (store (store arg16 arg17 ((_ extract 7 0) arg18)) (bvadd arg17 #x0000000000000001) ((_ extract 15 8) arg18)) (bvadd (bvadd arg17 #x0000000000000001) #x0000000000000001) ((_ extract 23 16) arg18)) (bvadd (bvadd (bvadd arg17 #x0000000000000001) #x0000000000000001) #x0000000000000001) ((_ extract 31 24) arg18)) (bvadd (bvadd (bvadd (bvadd arg17 #x0000000000000001) #x0000000000000001) #x0000000000000001) #x0000000000000001) ((_ extract 39 32) arg18)) (bvadd (bvadd (bvadd (bvadd (bvadd arg17 #x0000000000000001) #x0000000000000001) #x0000000000000001) #x0000000000000001) #x0000000000000001) ((_ extract 47 40) arg18)) (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd arg17 #x0000000000000001) #x0000000000000001) #x0000000000000001) #x0000000000000001) #x0000000000000001) #x0000000000000001) ((_ extract 55 48) arg18)) (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd arg17 #x0000000000000001) #x0000000000000001) #x0000000000000001) #x0000000000000001) #x0000000000000001) #x0000000000000001) #x0000000000000001) ((_ extract 63 56) arg18)))
(declare-fun fpop_literal16 ((_ BitVec 16) Bool (_ BitVec 16)) (_ BitVec 16))
(declare-fun fpop_literal32 ((_ BitVec 32) Bool (_ BitVec 32)) (_ BitVec 32))
(declare-fun fpop_literal64 ((_ BitVec 64) Bool (_ BitVec 64)) (_ BitVec 64))
(declare-fun fpop_bv_bitcast_to_fp16 ((_ BitVec 16)) (_ BitVec 16))
(declare-fun fpop_bv_bitcast_to_fp32 ((_ BitVec 32)) (_ BitVec 32))
(declare-fun fpop_bv_bitcast_to_fp64 ((_ BitVec 64)) (_ BitVec 64))
(declare-fun fpop_fp_bitcast_to_bv16 ((_ BitVec 16)) (_ BitVec 16))
(declare-fun fpop_fp_bitcast_to_bv32 ((_ BitVec 32)) (_ BitVec 32))
(declare-fun fpop_fp_bitcast_to_bv64 ((_ BitVec 64)) (_ BitVec 64))
(declare-fun fpop_fp_convert_to_fp16_16 ((_ BitVec 16)) (_ BitVec 16))
(declare-fun fpop_fp_convert_to_fp16_32 ((_ BitVec 16)) (_ BitVec 32))
(declare-fun fpop_fp_convert_to_fp16_64 ((_ BitVec 16)) (_ BitVec 64))
(declare-fun fpop_fp_convert_to_fp32_16 ((_ BitVec 32)) (_ BitVec 16))
(declare-fun fpop_fp_convert_to_fp32_32 ((_ BitVec 32)) (_ BitVec 32))
(declare-fun fpop_fp_convert_to_fp32_64 ((_ BitVec 32)) (_ BitVec 64))
(declare-fun fpop_fp_convert_to_fp64_16 ((_ BitVec 64)) (_ BitVec 16))
(declare-fun fpop_fp_convert_to_fp64_32 ((_ BitVec 64)) (_ BitVec 32))
(declare-fun fpop_fp_convert_to_fp64_64 ((_ BitVec 64)) (_ BitVec 64))
(declare-fun fpop_fp_convert_to_int16_32 ((_ BitVec 16)) (_ BitVec 32))
(declare-fun fpop_fp_convert_to_int16_64 ((_ BitVec 16)) (_ BitVec 64))
(declare-fun fpop_fp_convert_to_int32_32 ((_ BitVec 32)) (_ BitVec 32))
(declare-fun fpop_fp_convert_to_int32_64 ((_ BitVec 32)) (_ BitVec 64))
(declare-fun fpop_fp_convert_to_int64_32 ((_ BitVec 64)) (_ BitVec 32))
(declare-fun fpop_fp_convert_to_int64_64 ((_ BitVec 64)) (_ BitVec 64))
(declare-fun fpop_int_convert_to_fp16_32 ((_ BitVec 32)) (_ BitVec 16))
(declare-fun fpop_int_convert_to_fp16_64 ((_ BitVec 64)) (_ BitVec 16))
(declare-fun fpop_int_convert_to_fp32_32 ((_ BitVec 32)) (_ BitVec 32))
(declare-fun fpop_int_convert_to_fp32_64 ((_ BitVec 64)) (_ BitVec 32))
(declare-fun fpop_int_convert_to_fp64_32 ((_ BitVec 32)) (_ BitVec 64))
(declare-fun fpop_int_convert_to_fp64_64 ((_ BitVec 64)) (_ BitVec 64))
(declare-fun fpop_add16 ((_ BitVec 16) (_ BitVec 16)) (_ BitVec 16))
(declare-fun fpop_add32 ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))
(declare-fun fpop_add64 ((_ BitVec 64) (_ BitVec 64)) (_ BitVec 64))
(declare-fun fpop_sub16 ((_ BitVec 16) (_ BitVec 16)) (_ BitVec 16))
(declare-fun fpop_sub32 ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))
(declare-fun fpop_sub64 ((_ BitVec 64) (_ BitVec 64)) (_ BitVec 64))
(declare-fun fpop_mul16 ((_ BitVec 16) (_ BitVec 16)) (_ BitVec 16))
(declare-fun fpop_mul32 ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))
(declare-fun fpop_mul64 ((_ BitVec 64) (_ BitVec 64)) (_ BitVec 64))
(declare-fun fpop_div16 ((_ BitVec 16) (_ BitVec 16)) (_ BitVec 16))
(declare-fun fpop_div32 ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))
(declare-fun fpop_div64 ((_ BitVec 64) (_ BitVec 64)) (_ BitVec 64))
(declare-fun fpop_sqrt16 ((_ BitVec 16)) (_ BitVec 16))
(declare-fun fpop_sqrt32 ((_ BitVec 32)) (_ BitVec 32))
(declare-fun fpop_sqrt64 ((_ BitVec 64)) (_ BitVec 64))
(declare-fun fpop_le16 ((_ BitVec 16) (_ BitVec 16)) Bool)
(declare-fun fpop_le32 ((_ BitVec 32) (_ BitVec 32)) Bool)
(declare-fun fpop_le64 ((_ BitVec 64) (_ BitVec 64)) Bool)
(declare-fun fpop_lt16 ((_ BitVec 16) (_ BitVec 16)) Bool)
(declare-fun fpop_lt32 ((_ BitVec 32) (_ BitVec 32)) Bool)
(declare-fun fpop_lt64 ((_ BitVec 64) (_ BitVec 64)) Bool)
(declare-fun fpop_max16 ((_ BitVec 16) (_ BitVec 16)) Bool)
(declare-fun fpop_max32 ((_ BitVec 32) (_ BitVec 32)) Bool)
(declare-fun fpop_max64 ((_ BitVec 64) (_ BitVec 64)) Bool)
(declare-fun fpop_min16 ((_ BitVec 16) (_ BitVec 16)) Bool)
(declare-fun fpop_min32 ((_ BitVec 32) (_ BitVec 32)) Bool)
(declare-fun fpop_min64 ((_ BitVec 64) (_ BitVec 64)) Bool)
(declare-fun fpop_ordered16 ((_ BitVec 16) (_ BitVec 16)) Bool)
(declare-fun fpop_ordered32 ((_ BitVec 32) (_ BitVec 32)) Bool)
(declare-fun fpop_ordered64 ((_ BitVec 64) (_ BitVec 64)) Bool)
(declare-fun fnstart_rax () (_ BitVec 64))
(declare-fun fnstart_rcx () (_ BitVec 64))
(declare-fun fnstart_rdx () (_ BitVec 64))
(declare-fun fnstart_rbx () (_ BitVec 64))
(declare-fun fnstart_rsp () (_ BitVec 64))
(declare-fun fnstart_rbp () (_ BitVec 64))
(declare-fun fnstart_rsi () (_ BitVec 64))
(declare-fun fnstart_rdi () (_ BitVec 64))
(declare-fun fnstart_r8 () (_ BitVec 64))
(declare-fun fnstart_r9 () (_ BitVec 64))
(declare-fun fnstart_r10 () (_ BitVec 64))
(declare-fun fnstart_r11 () (_ BitVec 64))
(declare-fun fnstart_r12 () (_ BitVec 64))
(declare-fun fnstart_r13 () (_ BitVec 64))
(declare-fun fnstart_r14 () (_ BitVec 64))
(declare-fun fnstart_r15 () (_ BitVec 64))
(declare-fun fnstart_cf () Bool)
(declare-fun fnstart_RESERVED_1 () Bool)
(declare-fun fnstart_pf () Bool)
(declare-fun fnstart_RESERVED_3 () Bool)
(declare-fun fnstart_af () Bool)
(declare-fun fnstart_RESERVED_5 () Bool)
(declare-fun fnstart_zf () Bool)
(declare-fun fnstart_sf () Bool)
(declare-fun fnstart_tf () Bool)
(declare-fun fnstart_if () Bool)
(define-fun fnstart_df () Bool false)
(declare-fun fnstart_of () Bool)
(declare-fun fnstart_iopl1 () Bool)
(declare-fun fnstart_iopl2 () Bool)
(declare-fun fnstart_nt () Bool)
(declare-fun fnstart_RESERVED_15 () Bool)
(declare-fun fnstart_rf () Bool)
(declare-fun fnstart_vm () Bool)
(declare-fun fnstart_ac () Bool)
(declare-fun fnstart_vif () Bool)
(declare-fun fnstart_vip () Bool)
(declare-fun fnstart_id () Bool)
(declare-fun fnstart_el () Bool)
(declare-fun fnstart_el0 () Bool)
(declare-fun fnstart_el1 () Bool)
(declare-fun fnstart_el2 () Bool)
(declare-fun fnstart_el3 () Bool)
(declare-fun fnstart_el4 () Bool)
(declare-fun fnstart_el5 () Bool)
(declare-fun fnstart_el6 () Bool)
(declare-fun fnstart_el7 () Bool)
(declare-fun fnstart_el8 () Bool)
(declare-fun fnstart_xmm0 () (_ BitVec 512))
(declare-fun fnstart_xmm1 () (_ BitVec 512))
(declare-fun fnstart_xmm2 () (_ BitVec 512))
(declare-fun fnstart_xmm3 () (_ BitVec 512))
(declare-fun fnstart_xmm4 () (_ BitVec 512))
(declare-fun fnstart_xmm5 () (_ BitVec 512))
(declare-fun fnstart_xmm6 () (_ BitVec 512))
(declare-fun fnstart_xmm7 () (_ BitVec 512))
(declare-fun fnstart_xmm8 () (_ BitVec 512))
(declare-fun fnstart_xmm9 () (_ BitVec 512))
(declare-fun fnstart_xmm10 () (_ BitVec 512))
(declare-fun fnstart_xmm11 () (_ BitVec 512))
(declare-fun fnstart_xmm12 () (_ BitVec 512))
(declare-fun fnstart_xmm13 () (_ BitVec 512))
(declare-fun fnstart_xmm14 () (_ BitVec 512))
(declare-fun fnstart_xmm15 () (_ BitVec 512))
(declare-fun init_mem () (Array (_ BitVec 64) (_ BitVec 8)))
(declare-fun stack_alloc_min () (_ BitVec 64))
(assert (= (bvand stack_alloc_min #x0000000000000fff) #x0000000000000000))
(assert (bvult #x0000000000001000 stack_alloc_min))
(define-fun stack_guard_min () (_ BitVec 64) (bvsub stack_alloc_min #x0000000000001000))
(assert (bvult stack_guard_min stack_alloc_min))
(declare-fun stack_max () (_ BitVec 64))
(assert (= (bvand stack_max #x0000000000000fff) #x0000000000000000))
(assert (bvult stack_alloc_min stack_max))
(assert (bvule stack_alloc_min fnstart_rsp))
(assert (bvule fnstart_rsp (bvsub stack_max #x0000000000000008)))
(define-fun on_stack ((arg19 (_ BitVec 64)) (arg20 (_ BitVec 64))) Bool (let ((e (bvadd arg19 arg20))) (and (bvule stack_guard_min arg19) (and (bvule arg19 e) (bvule e stack_max)))))
(define-fun not_in_stack_range ((arg21 (_ BitVec 64)) (arg22 (_ BitVec 64))) Bool (let ((e0 (bvadd arg21 arg22))) (and (bvule arg21 e0) (or (bvule e0 stack_alloc_min) (bvule stack_max arg21)))))
(assert (bvult fnstart_rsp (bvsub stack_max #x0000000000000008)))
(assert (= (bvand (bvadd fnstart_rsp #x0000000000000008) #x000000000000000f) #x0000000000000000))
(define-fun is_in_mc_only_stack_range ((arg23 (_ BitVec 64)) (arg24 (_ BitVec 64))) Bool (let ((e1 (bvadd arg23 arg24))) (on_stack arg23 arg24)))
(declare-fun a0x201017_rax () (_ BitVec 64))
(declare-fun a0x201017_rcx () (_ BitVec 64))
(declare-fun a0x201017_rdx () (_ BitVec 64))
(declare-fun a0x201017_rbx () (_ BitVec 64))
(declare-fun a0x201017_rsp () (_ BitVec 64))
(declare-fun a0x201017_rbp () (_ BitVec 64))
(declare-fun a0x201017_rsi () (_ BitVec 64))
(declare-fun a0x201017_rdi () (_ BitVec 64))
(declare-fun a0x201017_r8 () (_ BitVec 64))
(declare-fun a0x201017_r9 () (_ BitVec 64))
(declare-fun a0x201017_r10 () (_ BitVec 64))
(declare-fun a0x201017_r11 () (_ BitVec 64))
(declare-fun a0x201017_r12 () (_ BitVec 64))
(declare-fun a0x201017_r13 () (_ BitVec 64))
(declare-fun a0x201017_r14 () (_ BitVec 64))
(declare-fun a0x201017_r15 () (_ BitVec 64))
(declare-fun a0x201017_cf () Bool)
(declare-fun a0x201017_RESERVED_1 () Bool)
(declare-fun a0x201017_pf () Bool)
(declare-fun a0x201017_RESERVED_3 () Bool)
(declare-fun a0x201017_af () Bool)
(declare-fun a0x201017_RESERVED_5 () Bool)
(declare-fun a0x201017_zf () Bool)
(declare-fun a0x201017_sf () Bool)
(declare-fun a0x201017_tf () Bool)
(declare-fun a0x201017_if () Bool)
(define-fun a0x201017_df () Bool false)
(declare-fun a0x201017_of () Bool)
(declare-fun a0x201017_iopl1 () Bool)
(declare-fun a0x201017_iopl2 () Bool)
(declare-fun a0x201017_nt () Bool)
(declare-fun a0x201017_RESERVED_15 () Bool)
(declare-fun a0x201017_rf () Bool)
(declare-fun a0x201017_vm () Bool)
(declare-fun a0x201017_ac () Bool)
(declare-fun a0x201017_vif () Bool)
(declare-fun a0x201017_vip () Bool)
(declare-fun a0x201017_id () Bool)
(declare-fun a0x201017_el () Bool)
(declare-fun a0x201017_el0 () Bool)
(declare-fun a0x201017_el1 () Bool)
(declare-fun a0x201017_el2 () Bool)
(declare-fun a0x201017_el3 () Bool)
(declare-fun a0x201017_el4 () Bool)
(declare-fun a0x201017_el5 () Bool)
(declare-fun a0x201017_el6 () Bool)
(declare-fun a0x201017_el7 () Bool)
(declare-fun a0x201017_el8 () Bool)
(declare-fun a0x201017_xmm0 () (_ BitVec 512))
(declare-fun a0x201017_xmm1 () (_ BitVec 512))
(declare-fun a0x201017_xmm2 () (_ BitVec 512))
(declare-fun a0x201017_xmm3 () (_ BitVec 512))
(declare-fun a0x201017_xmm4 () (_ BitVec 512))
(declare-fun a0x201017_xmm5 () (_ BitVec 512))
(declare-fun a0x201017_xmm6 () (_ BitVec 512))
(declare-fun a0x201017_xmm7 () (_ BitVec 512))
(declare-fun a0x201017_xmm8 () (_ BitVec 512))
(declare-fun a0x201017_xmm9 () (_ BitVec 512))
(declare-fun a0x201017_xmm10 () (_ BitVec 512))
(declare-fun a0x201017_xmm11 () (_ BitVec 512))
(declare-fun a0x201017_xmm12 () (_ BitVec 512))
(declare-fun a0x201017_xmm13 () (_ BitVec 512))
(declare-fun a0x201017_xmm14 () (_ BitVec 512))
(declare-fun a0x201017_xmm15 () (_ BitVec 512))
(define-fun %arg0 () (_ BitVec 64) fnstart_rdi)
(declare-fun %t4 () (_ BitVec 64))
(assert (= %t4 a0x201017_rdi))
(assert (= %t4 (mem_readbv64 init_mem (bvsub fnstart_rsp #x0000000000000018))))
(assert (= a0x201017_rbx fnstart_rbx))
(assert (= a0x201017_rsp (bvsub fnstart_rsp #x0000000000000028)))
(assert (= a0x201017_rbp (bvsub fnstart_rsp #x0000000000000008)))
(assert (= a0x201017_r12 fnstart_r12))
(assert (= a0x201017_r13 fnstart_r13))
(assert (= a0x201017_r14 fnstart_r14))
(assert (= a0x201017_r15 fnstart_r15))
(assert (= a0x201017_rdi (mem_readbv64 init_mem (bvsub fnstart_rsp #x0000000000000018))))
(assert (= (mem_readbv64 init_mem (bvsub fnstart_rsp #x0000000000000008)) fnstart_rbp))
; LLVM:     jump label %block_0_201058
(define-fun addr () (_ BitVec 64) (bvadd a0x201017_rbp (bvadd (bvmul #x0000000000000001 #x0000000000000000) #xfffffffffffffff0)))
(declare-fun readv () (_ BitVec 64))
(assert (on_stack addr #x0000000000000008))
(assert (= readv (mem_readbv64 init_mem addr)))
(define-fun addr0 () (_ BitVec 64) (bvadd a0x201017_rbp (bvadd (bvmul #x0000000000000001 #x0000000000000000) #xfffffffffffffff8)))
(assert (is_in_mc_only_stack_range addr0 #x0000000000000008))
(define-fun mem () (Array (_ BitVec 64) (_ BitVec 8)) (mem_writebv64 init_mem addr0 (ite true readv a0x201017_rax)))
(assert (= (bvadd #x0000000000201024 ((_ sign_extend 32) #x00000034)) #x0000000000201058))
(check-sat-assuming ((not (= a0x201017_df false))))
(exit)
