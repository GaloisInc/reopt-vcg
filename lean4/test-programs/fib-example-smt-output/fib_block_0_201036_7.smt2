; fib.block_0_201036.2 (0x201048). Checking jump register x87top.
(set-logic ALL_SUPPORTED)
(set-option :produce-models true)
(define-fun even_parity ((v (_ BitVec 8))) Bool (= (bvxor ((_ extract 0 0) v) ((_ extract 1 1) v) ((_ extract 2 2) v) ((_ extract 3 3) v) ((_ extract 4 4) v) ((_ extract 5 5) v) ((_ extract 6 6) v) ((_ extract 7 7) v)) #b0))
(define-fun mem_readbv8 ((m (Array (_ BitVec 64) (_ BitVec 8))) (a (_ BitVec 64))) (_ BitVec 8) (select m a))
(define-fun mem_readbv16 ((m (Array (_ BitVec 64) (_ BitVec 8))) (a (_ BitVec 64))) (_ BitVec 16) (concat (select m (bvadd a (_ bv1 64))) (select m a)))
(define-fun mem_readbv32 ((m (Array (_ BitVec 64) (_ BitVec 8))) (a (_ BitVec 64))) (_ BitVec 32) (concat (select m (bvadd a (_ bv3 64))) (concat (select m (bvadd a (_ bv2 64))) (concat (select m (bvadd a (_ bv1 64))) (select m a)))))
(define-fun mem_readbv64 ((m (Array (_ BitVec 64) (_ BitVec 8))) (a (_ BitVec 64))) (_ BitVec 64) (concat (select m (bvadd a (_ bv7 64))) (concat (select m (bvadd a (_ bv6 64))) (concat (select m (bvadd a (_ bv5 64))) (concat (select m (bvadd a (_ bv4 64))) (concat (select m (bvadd a (_ bv3 64))) (concat (select m (bvadd a (_ bv2 64))) (concat (select m (bvadd a (_ bv1 64))) (select m a)))))))))
(define-fun mem_writebv8 ((m (Array (_ BitVec 64) (_ BitVec 8))) (a (_ BitVec 64)) (v (_ BitVec 8))) (Array (_ BitVec 64) (_ BitVec 8)) (store m a ((_ extract 7 0) v)))
(define-fun mem_writebv16 ((m (Array (_ BitVec 64) (_ BitVec 8))) (a (_ BitVec 64)) (v (_ BitVec 16))) (Array (_ BitVec 64) (_ BitVec 8)) (store (store m a ((_ extract 7 0) v)) (bvadd a (_ bv1 64)) ((_ extract 15 8) v)))
(define-fun mem_writebv32 ((m (Array (_ BitVec 64) (_ BitVec 8))) (a (_ BitVec 64)) (v (_ BitVec 32))) (Array (_ BitVec 64) (_ BitVec 8)) (store (store (store (store m a ((_ extract 7 0) v)) (bvadd a (_ bv1 64)) ((_ extract 15 8) v)) (bvadd a (_ bv2 64)) ((_ extract 23 16) v)) (bvadd a (_ bv3 64)) ((_ extract 31 24) v)))
(define-fun mem_writebv64 ((m (Array (_ BitVec 64) (_ BitVec 8))) (a (_ BitVec 64)) (v (_ BitVec 64))) (Array (_ BitVec 64) (_ BitVec 8)) (store (store (store (store (store (store (store (store m a ((_ extract 7 0) v)) (bvadd a (_ bv1 64)) ((_ extract 15 8) v)) (bvadd a (_ bv2 64)) ((_ extract 23 16) v)) (bvadd a (_ bv3 64)) ((_ extract 31 24) v)) (bvadd a (_ bv4 64)) ((_ extract 39 32) v)) (bvadd a (_ bv5 64)) ((_ extract 47 40) v)) (bvadd a (_ bv6 64)) ((_ extract 55 48) v)) (bvadd a (_ bv7 64)) ((_ extract 63 56) v)))
(declare-fun fnstart_rcx () (_ BitVec 64))
(declare-fun fnstart_rdx () (_ BitVec 64))
(declare-fun fnstart_rbx () (_ BitVec 64))
(declare-fun fnstart_rsp () (_ BitVec 64))
(declare-fun fnstart_rbp () (_ BitVec 64))
(declare-fun fnstart_rsi () (_ BitVec 64))
(declare-fun fnstart_rdi () (_ BitVec 64))
(declare-fun fnstart_r8 () (_ BitVec 64))
(declare-fun fnstart_r9 () (_ BitVec 64))
(declare-fun fnstart_r12 () (_ BitVec 64))
(declare-fun fnstart_r13 () (_ BitVec 64))
(declare-fun fnstart_r14 () (_ BitVec 64))
(declare-fun fnstart_r15 () (_ BitVec 64))
(declare-const stack_alloc_min (_ BitVec 64))
(assert (= (bvand stack_alloc_min #x0000000000000fff) (_ bv0 64)))
(assert (bvult (_ bv4096 64) stack_alloc_min))
(define-fun stack_guard_min () (_ BitVec 64) (bvsub stack_alloc_min (_ bv4096 64)))
(assert (bvult stack_guard_min stack_alloc_min))
(declare-const stack_max (_ BitVec 64))
(assert (= (bvand stack_max #x0000000000000fff) (_ bv0 64)))
(assert (bvult stack_alloc_min stack_max))
(assert (bvule stack_alloc_min fnstart_rsp))
(assert (bvule fnstart_rsp (bvsub stack_max (_ bv8 64))))
(define-fun on_stack ((a (_ BitVec 64)) (sz (_ BitVec 64))) Bool (let ((e (bvadd a sz))) (and (bvule stack_guard_min a) (bvule a e) (bvule e stack_max))))
(define-fun not_in_stack_range ((a (_ BitVec 64)) (sz (_ BitVec 64))) Bool (let ((e (bvadd a sz))) (and (bvule a e) (or (bvule e stack_alloc_min) (bvule stack_max a)))))
(assert (bvult fnstart_rsp (bvsub stack_max (_ bv8 64))))
(assert (= ((_ extract 3 0) fnstart_rsp) (_ bv8 4)))
(define-fun mc_only_stack_range ((a (_ BitVec 64)) (sz (_ BitVec 64))) Bool (let ((e (bvadd a sz))) (on_stack a sz)))
(define-fun a201036_rip () (_ BitVec 64) #x0000000000201036)
(declare-fun a201036_rax () (_ BitVec 64))
(declare-fun a201036_rcx () (_ BitVec 64))
(declare-fun a201036_rdx () (_ BitVec 64))
(declare-fun a201036_rbx () (_ BitVec 64))
(declare-fun a201036_rsp () (_ BitVec 64))
(declare-fun a201036_rbp () (_ BitVec 64))
(declare-fun a201036_rsi () (_ BitVec 64))
(declare-fun a201036_rdi () (_ BitVec 64))
(declare-fun a201036_r8 () (_ BitVec 64))
(declare-fun a201036_r9 () (_ BitVec 64))
(declare-fun a201036_r10 () (_ BitVec 64))
(declare-fun a201036_r11 () (_ BitVec 64))
(declare-fun a201036_r12 () (_ BitVec 64))
(declare-fun a201036_r13 () (_ BitVec 64))
(declare-fun a201036_r14 () (_ BitVec 64))
(declare-fun a201036_r15 () (_ BitVec 64))
(declare-fun a201036_cf () Bool)
(declare-fun a201036_pf () Bool)
(declare-fun a201036_af () Bool)
(declare-fun a201036_zf () Bool)
(declare-fun a201036_sf () Bool)
(declare-fun a201036_tf () Bool)
(declare-fun a201036_if () Bool)
(define-fun a201036_df () Bool false)
(declare-fun a201036_of () Bool)
(declare-fun a201036_ie () Bool)
(declare-fun a201036_de () Bool)
(declare-fun a201036_ze () Bool)
(declare-fun a201036_oe () Bool)
(declare-fun a201036_ue () Bool)
(declare-fun a201036_pe () Bool)
(declare-fun a201036_ef () Bool)
(declare-fun a201036_es () Bool)
(declare-fun a201036_c0 () Bool)
(declare-fun a201036_c1 () Bool)
(declare-fun a201036_c2 () Bool)
(declare-fun a201036_RESERVED_STATUS_11 () Bool)
(declare-fun a201036_RESERVED_STATUS_12 () Bool)
(declare-fun a201036_RESERVED_STATUS_13 () Bool)
(declare-fun a201036_c3 () Bool)
(declare-fun a201036_RESERVED_STATUS_15 () Bool)
(define-fun a201036_x87top () (_ BitVec 3) (_ bv7 3))
(declare-fun a201036_tag0 () (_ BitVec 2))
(declare-fun a201036_tag1 () (_ BitVec 2))
(declare-fun a201036_tag2 () (_ BitVec 2))
(declare-fun a201036_tag3 () (_ BitVec 2))
(declare-fun a201036_tag4 () (_ BitVec 2))
(declare-fun a201036_tag5 () (_ BitVec 2))
(declare-fun a201036_tag6 () (_ BitVec 2))
(declare-fun a201036_tag7 () (_ BitVec 2))
(declare-fun a201036_mm0 () (_ BitVec 80))
(declare-fun a201036_mm1 () (_ BitVec 80))
(declare-fun a201036_mm2 () (_ BitVec 80))
(declare-fun a201036_mm3 () (_ BitVec 80))
(declare-fun a201036_mm4 () (_ BitVec 80))
(declare-fun a201036_mm5 () (_ BitVec 80))
(declare-fun a201036_mm6 () (_ BitVec 80))
(declare-fun a201036_mm7 () (_ BitVec 80))
(declare-fun a201036_zmm0 () (_ BitVec 512))
(declare-fun a201036_zmm1 () (_ BitVec 512))
(declare-fun a201036_zmm2 () (_ BitVec 512))
(declare-fun a201036_zmm3 () (_ BitVec 512))
(declare-fun a201036_zmm4 () (_ BitVec 512))
(declare-fun a201036_zmm5 () (_ BitVec 512))
(declare-fun a201036_zmm6 () (_ BitVec 512))
(declare-fun a201036_zmm7 () (_ BitVec 512))
(declare-fun a201036_zmm8 () (_ BitVec 512))
(declare-fun a201036_zmm9 () (_ BitVec 512))
(declare-fun a201036_zmm10 () (_ BitVec 512))
(declare-fun a201036_zmm11 () (_ BitVec 512))
(declare-fun a201036_zmm12 () (_ BitVec 512))
(declare-fun a201036_zmm13 () (_ BitVec 512))
(declare-fun a201036_zmm14 () (_ BitVec 512))
(declare-fun a201036_zmm15 () (_ BitVec 512))
(declare-fun a201036_zmm16 () (_ BitVec 512))
(declare-fun a201036_zmm17 () (_ BitVec 512))
(declare-fun a201036_zmm18 () (_ BitVec 512))
(declare-fun a201036_zmm19 () (_ BitVec 512))
(declare-fun a201036_zmm20 () (_ BitVec 512))
(declare-fun a201036_zmm21 () (_ BitVec 512))
(declare-fun a201036_zmm22 () (_ BitVec 512))
(declare-fun a201036_zmm23 () (_ BitVec 512))
(declare-fun a201036_zmm24 () (_ BitVec 512))
(declare-fun a201036_zmm25 () (_ BitVec 512))
(declare-fun a201036_zmm26 () (_ BitVec 512))
(declare-fun a201036_zmm27 () (_ BitVec 512))
(declare-fun a201036_zmm28 () (_ BitVec 512))
(declare-fun a201036_zmm29 () (_ BitVec 512))
(declare-fun a201036_zmm30 () (_ BitVec 512))
(declare-fun a201036_zmm31 () (_ BitVec 512))
(declare-const x86mem_0 (Array (_ BitVec 64) (_ BitVec 8)))
(define-fun return_addr () (_ BitVec 64) (mem_readbv64 x86mem_0 fnstart_rsp))
(define-fun llvm_arg0 () (_ BitVec 64) fnstart_rdi)
(declare-const llvm_t8 (_ BitVec 64))
(declare-const llvm_t9 (_ BitVec 64))
(assert (= llvm_t8 a201036_rax))
(assert (= llvm_t9 (mem_readbv64 x86mem_0 (bvsub fnstart_rsp (_ bv24 64)))))
(assert (= a201036_rbx fnstart_rbx))
(assert (= a201036_rsp (bvsub fnstart_rsp (_ bv40 64))))
(assert (= a201036_rbp (bvsub fnstart_rsp (_ bv8 64))))
(assert (= a201036_r12 fnstart_r12))
(assert (= a201036_r13 fnstart_r13))
(assert (= a201036_r14 fnstart_r14))
(assert (= a201036_r15 fnstart_r15))
(assert (= (mem_readbv64 x86mem_0 (bvsub fnstart_rsp (_ bv8 64))) fnstart_rbp))
; LLVM: %t10 = add i64 %t9, 18446744073709551614
(define-fun llvm_t10 () (_ BitVec 64) (bvadd llvm_t9 (_ bv18446744073709551614 64)))
; LLVM: %t11 = call i64 (i64) @fib(i64 %t10)
(define-fun x86local_0 () (_ BitVec 64) (bvadd a201036_rbp (_ bv18446744073709551600 64)))
(assert (on_stack x86local_0 (_ bv8 64)))
(define-fun x86local_1 () (_ BitVec 64) (mem_readbv64 x86mem_0 x86local_0))
(define-fun x86local_2 () Bool (distinct ((_ extract 64 64) (bvsub (bvsub ((_ sign_extend 1) x86local_1) (bvneg ((_ sign_extend 1) (_ bv2 64)))) (ite false (_ bv1 65) (_ bv0 65)))) ((_ extract 63 63) (bvsub (bvsub ((_ sign_extend 1) x86local_1) (bvneg ((_ sign_extend 1) (_ bv2 64)))) (ite false (_ bv1 65) (_ bv0 65))))))
(define-fun x86local_3 () (_ BitVec 4) ((_ extract 3 0) x86local_1))
(define-fun x86local_4 () Bool (bvult x86local_3 (_ bv2 4)))
(define-fun x86local_5 () Bool (bvult x86local_1 (_ bv2 64)))
(define-fun x86local_6 () (_ BitVec 64) (bvsub x86local_1 (_ bv2 64)))
(define-fun x86local_7 () Bool (bvslt x86local_6 (_ bv0 64)))
(define-fun x86local_8 () Bool (= x86local_6 (_ bv0 64)))
(define-fun x86local_9 () (_ BitVec 8) ((_ extract 7 0) x86local_6))
(define-fun x86local_10 () Bool (even_parity x86local_9))
(define-fun x86local_11 () (_ BitVec 64) (bvadd a201036_rbp (_ bv18446744073709551592 64)))
(assert (mc_only_stack_range x86local_11 (_ bv8 64)))
(define-fun x86mem_1 () (Array (_ BitVec 64) (_ BitVec 8)) (mem_writebv64 x86mem_0 x86local_11 a201036_rax))
(define-fun x86local_12 () (_ BitVec 64) (bvsub a201036_rsp (_ bv8 64)))
(assert (mc_only_stack_range x86local_12 (_ bv8 64)))
(define-fun x86mem_2 () (Array (_ BitVec 64) (_ BitVec 8)) (mem_writebv64 x86mem_1 x86local_12 #x000000000020104d))
(assert (= #x0000000000201000 #x0000000000201000))
(assert (= llvm_t10 x86local_6))
(assert (= (mem_readbv64 x86mem_2 x86local_12) #x000000000020104d))
(define-fun a20104d_rip () (_ BitVec 64) #x000000000020104d)
(declare-fun a20104d_rax () (_ BitVec 64))
(declare-fun a20104d_rcx () (_ BitVec 64))
(declare-fun a20104d_rdx () (_ BitVec 64))
(define-fun a20104d_rbx () (_ BitVec 64) a201036_rbx)
(define-fun a20104d_rsp () (_ BitVec 64) (bvadd x86local_12 (_ bv8 64)))
(define-fun a20104d_rbp () (_ BitVec 64) a201036_rbp)
(declare-fun a20104d_rsi () (_ BitVec 64))
(declare-fun a20104d_rdi () (_ BitVec 64))
(declare-fun a20104d_r8 () (_ BitVec 64))
(declare-fun a20104d_r9 () (_ BitVec 64))
(declare-fun a20104d_r10 () (_ BitVec 64))
(declare-fun a20104d_r11 () (_ BitVec 64))
(define-fun a20104d_r12 () (_ BitVec 64) a201036_r12)
(define-fun a20104d_r13 () (_ BitVec 64) a201036_r13)
(define-fun a20104d_r14 () (_ BitVec 64) a201036_r14)
(define-fun a20104d_r15 () (_ BitVec 64) a201036_r15)
(declare-fun a20104d_cf () Bool)
(declare-fun a20104d_pf () Bool)
(declare-fun a20104d_af () Bool)
(declare-fun a20104d_zf () Bool)
(declare-fun a20104d_sf () Bool)
(declare-fun a20104d_tf () Bool)
(declare-fun a20104d_if () Bool)
(define-fun a20104d_df () Bool false)
(declare-fun a20104d_of () Bool)
(declare-fun a20104d_ie () Bool)
(declare-fun a20104d_de () Bool)
(declare-fun a20104d_ze () Bool)
(declare-fun a20104d_oe () Bool)
(declare-fun a20104d_ue () Bool)
(declare-fun a20104d_pe () Bool)
(declare-fun a20104d_ef () Bool)
(declare-fun a20104d_es () Bool)
(declare-fun a20104d_c0 () Bool)
(declare-fun a20104d_c1 () Bool)
(declare-fun a20104d_c2 () Bool)
(declare-fun a20104d_RESERVED_STATUS_11 () Bool)
(declare-fun a20104d_RESERVED_STATUS_12 () Bool)
(declare-fun a20104d_RESERVED_STATUS_13 () Bool)
(declare-fun a20104d_c3 () Bool)
(declare-fun a20104d_RESERVED_STATUS_15 () Bool)
(define-fun a20104d_x87top () (_ BitVec 3) (_ bv7 3))
(declare-fun a20104d_tag0 () (_ BitVec 2))
(declare-fun a20104d_tag1 () (_ BitVec 2))
(declare-fun a20104d_tag2 () (_ BitVec 2))
(declare-fun a20104d_tag3 () (_ BitVec 2))
(declare-fun a20104d_tag4 () (_ BitVec 2))
(declare-fun a20104d_tag5 () (_ BitVec 2))
(declare-fun a20104d_tag6 () (_ BitVec 2))
(declare-fun a20104d_tag7 () (_ BitVec 2))
(declare-fun a20104d_mm0 () (_ BitVec 80))
(declare-fun a20104d_mm1 () (_ BitVec 80))
(declare-fun a20104d_mm2 () (_ BitVec 80))
(declare-fun a20104d_mm3 () (_ BitVec 80))
(declare-fun a20104d_mm4 () (_ BitVec 80))
(declare-fun a20104d_mm5 () (_ BitVec 80))
(declare-fun a20104d_mm6 () (_ BitVec 80))
(declare-fun a20104d_mm7 () (_ BitVec 80))
(declare-fun a20104d_zmm0 () (_ BitVec 512))
(declare-fun a20104d_zmm1 () (_ BitVec 512))
(declare-fun a20104d_zmm2 () (_ BitVec 512))
(declare-fun a20104d_zmm3 () (_ BitVec 512))
(declare-fun a20104d_zmm4 () (_ BitVec 512))
(declare-fun a20104d_zmm5 () (_ BitVec 512))
(declare-fun a20104d_zmm6 () (_ BitVec 512))
(declare-fun a20104d_zmm7 () (_ BitVec 512))
(declare-fun a20104d_zmm8 () (_ BitVec 512))
(declare-fun a20104d_zmm9 () (_ BitVec 512))
(declare-fun a20104d_zmm10 () (_ BitVec 512))
(declare-fun a20104d_zmm11 () (_ BitVec 512))
(declare-fun a20104d_zmm12 () (_ BitVec 512))
(declare-fun a20104d_zmm13 () (_ BitVec 512))
(declare-fun a20104d_zmm14 () (_ BitVec 512))
(declare-fun a20104d_zmm15 () (_ BitVec 512))
(declare-fun a20104d_zmm16 () (_ BitVec 512))
(declare-fun a20104d_zmm17 () (_ BitVec 512))
(declare-fun a20104d_zmm18 () (_ BitVec 512))
(declare-fun a20104d_zmm19 () (_ BitVec 512))
(declare-fun a20104d_zmm20 () (_ BitVec 512))
(declare-fun a20104d_zmm21 () (_ BitVec 512))
(declare-fun a20104d_zmm22 () (_ BitVec 512))
(declare-fun a20104d_zmm23 () (_ BitVec 512))
(declare-fun a20104d_zmm24 () (_ BitVec 512))
(declare-fun a20104d_zmm25 () (_ BitVec 512))
(declare-fun a20104d_zmm26 () (_ BitVec 512))
(declare-fun a20104d_zmm27 () (_ BitVec 512))
(declare-fun a20104d_zmm28 () (_ BitVec 512))
(declare-fun a20104d_zmm29 () (_ BitVec 512))
(declare-fun a20104d_zmm30 () (_ BitVec 512))
(declare-fun a20104d_zmm31 () (_ BitVec 512))
(declare-const x86mem_3 (Array (_ BitVec 64) (_ BitVec 8)))
(assert (eqrange x86mem_3 x86mem_2 (bvadd x86local_12 (_ bv8 64)) (bvadd fnstart_rsp (_ bv7 64))))
(define-fun llvm_t11 () (_ BitVec 64) a20104d_rax)
; LLVM: br label %block_0_20104d
(assert (= #x000000000020104d a20104d_rip))
(check-sat-assuming ((not (= (_ bv7 3) a20104d_x87top))))
(exit)
