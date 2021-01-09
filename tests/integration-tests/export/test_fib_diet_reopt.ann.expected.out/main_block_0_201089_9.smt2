; main.block_0_201089.1 @ 0x201098: precondition ((= r13 (fnstart r13)), for jump)
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
(declare-fun fnstart_df () Bool)
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
(declare-fun fnstart_xmm0 () (_ BitVec 256))
(declare-fun fnstart_xmm1 () (_ BitVec 256))
(declare-fun fnstart_xmm2 () (_ BitVec 256))
(declare-fun fnstart_xmm3 () (_ BitVec 256))
(declare-fun fnstart_xmm4 () (_ BitVec 256))
(declare-fun fnstart_xmm5 () (_ BitVec 256))
(declare-fun fnstart_xmm6 () (_ BitVec 256))
(declare-fun fnstart_xmm7 () (_ BitVec 256))
(declare-fun fnstart_xmm8 () (_ BitVec 256))
(declare-fun fnstart_xmm9 () (_ BitVec 256))
(declare-fun fnstart_xmm10 () (_ BitVec 256))
(declare-fun fnstart_xmm11 () (_ BitVec 256))
(declare-fun fnstart_xmm12 () (_ BitVec 256))
(declare-fun fnstart_xmm13 () (_ BitVec 256))
(declare-fun fnstart_xmm14 () (_ BitVec 256))
(declare-fun fnstart_xmm15 () (_ BitVec 256))
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
(declare-fun a0x201089_rax () (_ BitVec 64))
(declare-fun a0x201089_rcx () (_ BitVec 64))
(declare-fun a0x201089_rdx () (_ BitVec 64))
(declare-fun a0x201089_rbx () (_ BitVec 64))
(declare-fun a0x201089_rsp () (_ BitVec 64))
(declare-fun a0x201089_rbp () (_ BitVec 64))
(declare-fun a0x201089_rsi () (_ BitVec 64))
(declare-fun a0x201089_rdi () (_ BitVec 64))
(declare-fun a0x201089_r8 () (_ BitVec 64))
(declare-fun a0x201089_r9 () (_ BitVec 64))
(declare-fun a0x201089_r10 () (_ BitVec 64))
(declare-fun a0x201089_r11 () (_ BitVec 64))
(declare-fun a0x201089_r12 () (_ BitVec 64))
(declare-fun a0x201089_r13 () (_ BitVec 64))
(declare-fun a0x201089_r14 () (_ BitVec 64))
(declare-fun a0x201089_r15 () (_ BitVec 64))
(declare-fun a0x201089_cf () Bool)
(declare-fun a0x201089_RESERVED_1 () Bool)
(declare-fun a0x201089_pf () Bool)
(declare-fun a0x201089_RESERVED_3 () Bool)
(declare-fun a0x201089_af () Bool)
(declare-fun a0x201089_RESERVED_5 () Bool)
(declare-fun a0x201089_zf () Bool)
(declare-fun a0x201089_sf () Bool)
(declare-fun a0x201089_tf () Bool)
(declare-fun a0x201089_if () Bool)
(declare-fun a0x201089_df () Bool)
(declare-fun a0x201089_of () Bool)
(declare-fun a0x201089_iopl1 () Bool)
(declare-fun a0x201089_iopl2 () Bool)
(declare-fun a0x201089_nt () Bool)
(declare-fun a0x201089_RESERVED_15 () Bool)
(declare-fun a0x201089_rf () Bool)
(declare-fun a0x201089_vm () Bool)
(declare-fun a0x201089_ac () Bool)
(declare-fun a0x201089_vif () Bool)
(declare-fun a0x201089_vip () Bool)
(declare-fun a0x201089_id () Bool)
(declare-fun a0x201089_el () Bool)
(declare-fun a0x201089_el0 () Bool)
(declare-fun a0x201089_el1 () Bool)
(declare-fun a0x201089_el2 () Bool)
(declare-fun a0x201089_el3 () Bool)
(declare-fun a0x201089_el4 () Bool)
(declare-fun a0x201089_el5 () Bool)
(declare-fun a0x201089_el6 () Bool)
(declare-fun a0x201089_el7 () Bool)
(declare-fun a0x201089_el8 () Bool)
(declare-fun a0x201089_xmm0 () (_ BitVec 256))
(declare-fun a0x201089_xmm1 () (_ BitVec 256))
(declare-fun a0x201089_xmm2 () (_ BitVec 256))
(declare-fun a0x201089_xmm3 () (_ BitVec 256))
(declare-fun a0x201089_xmm4 () (_ BitVec 256))
(declare-fun a0x201089_xmm5 () (_ BitVec 256))
(declare-fun a0x201089_xmm6 () (_ BitVec 256))
(declare-fun a0x201089_xmm7 () (_ BitVec 256))
(declare-fun a0x201089_xmm8 () (_ BitVec 256))
(declare-fun a0x201089_xmm9 () (_ BitVec 256))
(declare-fun a0x201089_xmm10 () (_ BitVec 256))
(declare-fun a0x201089_xmm11 () (_ BitVec 256))
(declare-fun a0x201089_xmm12 () (_ BitVec 256))
(declare-fun a0x201089_xmm13 () (_ BitVec 256))
(declare-fun a0x201089_xmm14 () (_ BitVec 256))
(declare-fun a0x201089_xmm15 () (_ BitVec 256))
(declare-fun %t1 () (_ BitVec 64))
(assert (= %t1 a0x201089_rax))
(assert (= a0x201089_rbx fnstart_rbx))
(assert (= a0x201089_rsp (bvsub fnstart_rsp #x0000000000000018)))
(assert (= a0x201089_rbp (bvsub fnstart_rsp #x0000000000000008)))
(assert (= a0x201089_r12 fnstart_r12))
(assert (= a0x201089_r13 fnstart_r13))
(assert (= a0x201089_r14 fnstart_r14))
(assert (= a0x201089_r15 fnstart_r15))
(assert (= (mem_readbv64 init_mem (bvsub fnstart_rsp #x0000000000000008)) fnstart_rbp))
; LLVM:     %t2 = call i64 @printf (i64 2097618,i64 %t1)
(define-fun rdi () (_ BitVec 64) ((_ sign_extend 0) #x00000000002001d2))
(define-fun rax () (_ BitVec 64) (bvor (bvand a0x201089_rax (bvnot (bvshl ((_ zero_extend 56) ((_ repeat 8) #b1)) #x0000000000000000))) (bvshl ((_ zero_extend 56) ((_ sign_extend 0) #x00)) #x0000000000000000)))
(define-fun rsp () (_ BitVec 64) (bvsub a0x201089_rsp #x0000000000000008))
(define-fun addr () (_ BitVec 64) (bvsub a0x201089_rsp #x0000000000000008))
(assert (is_in_mc_only_stack_range addr #x0000000000000008))
(define-fun mem () (Array (_ BitVec 64) (_ BitVec 8)) (mem_writebv64 init_mem addr #x000000000020109d))
(assert (= #x00000000002001d2 (ite true rdi a0x201089_rdi)))
(assert (= %t1 (ite true a0x201089_rax a0x201089_rsi)))
(assert (= (mem_readbv64 mem (ite true rsp a0x201089_rsp)) #x000000000020109d))
(declare-fun a0x20109d_xmm15 () (_ BitVec 256))
(declare-fun a0x20109d_xmm14 () (_ BitVec 256))
(declare-fun a0x20109d_xmm13 () (_ BitVec 256))
(declare-fun a0x20109d_xmm12 () (_ BitVec 256))
(declare-fun a0x20109d_xmm11 () (_ BitVec 256))
(declare-fun a0x20109d_xmm10 () (_ BitVec 256))
(declare-fun a0x20109d_xmm9 () (_ BitVec 256))
(declare-fun a0x20109d_xmm8 () (_ BitVec 256))
(declare-fun a0x20109d_xmm7 () (_ BitVec 256))
(declare-fun a0x20109d_xmm6 () (_ BitVec 256))
(declare-fun a0x20109d_xmm5 () (_ BitVec 256))
(declare-fun a0x20109d_xmm4 () (_ BitVec 256))
(declare-fun a0x20109d_xmm3 () (_ BitVec 256))
(declare-fun a0x20109d_xmm2 () (_ BitVec 256))
(declare-fun a0x20109d_xmm1 () (_ BitVec 256))
(declare-fun a0x20109d_xmm0 () (_ BitVec 256))
(declare-fun a0x20109d_el8 () Bool)
(declare-fun a0x20109d_el7 () Bool)
(declare-fun a0x20109d_el6 () Bool)
(declare-fun a0x20109d_el5 () Bool)
(declare-fun a0x20109d_el4 () Bool)
(declare-fun a0x20109d_el3 () Bool)
(declare-fun a0x20109d_el2 () Bool)
(declare-fun a0x20109d_el1 () Bool)
(declare-fun a0x20109d_el0 () Bool)
(declare-fun a0x20109d_el () Bool)
(declare-fun a0x20109d_id () Bool)
(declare-fun a0x20109d_vip () Bool)
(declare-fun a0x20109d_vif () Bool)
(declare-fun a0x20109d_ac () Bool)
(declare-fun a0x20109d_vm () Bool)
(declare-fun a0x20109d_rf () Bool)
(declare-fun a0x20109d_RESERVED_15 () Bool)
(declare-fun a0x20109d_nt () Bool)
(declare-fun a0x20109d_iopl2 () Bool)
(declare-fun a0x20109d_iopl1 () Bool)
(declare-fun a0x20109d_of () Bool)
(declare-fun a0x20109d_df () Bool)
(declare-fun a0x20109d_if () Bool)
(declare-fun a0x20109d_tf () Bool)
(declare-fun a0x20109d_sf () Bool)
(declare-fun a0x20109d_zf () Bool)
(declare-fun a0x20109d_RESERVED_5 () Bool)
(declare-fun a0x20109d_af () Bool)
(declare-fun a0x20109d_RESERVED_3 () Bool)
(declare-fun a0x20109d_pf () Bool)
(declare-fun a0x20109d_RESERVED_1 () Bool)
(declare-fun a0x20109d_cf () Bool)
(declare-fun a0x20109d_r15 () (_ BitVec 64))
(declare-fun a0x20109d_r14 () (_ BitVec 64))
(declare-fun a0x20109d_r13 () (_ BitVec 64))
(declare-fun a0x20109d_r12 () (_ BitVec 64))
(declare-fun a0x20109d_r11 () (_ BitVec 64))
(declare-fun a0x20109d_r10 () (_ BitVec 64))
(declare-fun a0x20109d_r9 () (_ BitVec 64))
(declare-fun a0x20109d_r8 () (_ BitVec 64))
(declare-fun a0x20109d_rdi () (_ BitVec 64))
(declare-fun a0x20109d_rsi () (_ BitVec 64))
(declare-fun a0x20109d_rbp () (_ BitVec 64))
(declare-fun a0x20109d_rsp () (_ BitVec 64))
(declare-fun a0x20109d_rbx () (_ BitVec 64))
(declare-fun a0x20109d_rdx () (_ BitVec 64))
(declare-fun a0x20109d_rcx () (_ BitVec 64))
(declare-fun a0x20109d_rax () (_ BitVec 64))
(declare-fun mem0 () (Array (_ BitVec 64) (_ BitVec 8)))
(assert (eqrange mem0 mem (bvadd (ite true rsp a0x201089_rsp) #x0000000000000008) (bvadd fnstart_rsp #x0000000000000007)))
(define-fun %t2 () (_ BitVec 64) a0x20109d_rax)
; LLVM:     jump label %block_0_20109d
(assert (= #x000000000020109d #x000000000020109d))
(assert (= a0x201089_rbx fnstart_rbx))
(assert (= (bvadd (ite true rsp a0x201089_rsp) #x0000000000000008) (bvsub fnstart_rsp #x0000000000000018)))
(assert (= a0x201089_rbp (bvsub fnstart_rsp #x0000000000000008)))
(assert (= a0x201089_r12 fnstart_r12))
(check-sat-assuming ((not (= a0x201089_r13 fnstart_r13))))
(exit)
