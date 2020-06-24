; fib.block_0_201017.0 (0x20101f). jump precondition: (= r13 (fnstart r13))
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
(define-fun a201017_rip () (_ BitVec 64) #x0000000000201017)
(declare-fun a201017_rax () (_ BitVec 64))
(declare-fun a201017_rcx () (_ BitVec 64))
(declare-fun a201017_rdx () (_ BitVec 64))
(declare-fun a201017_rbx () (_ BitVec 64))
(declare-fun a201017_rsp () (_ BitVec 64))
(declare-fun a201017_rbp () (_ BitVec 64))
(declare-fun a201017_rsi () (_ BitVec 64))
(declare-fun a201017_rdi () (_ BitVec 64))
(declare-fun a201017_r8 () (_ BitVec 64))
(declare-fun a201017_r9 () (_ BitVec 64))
(declare-fun a201017_r10 () (_ BitVec 64))
(declare-fun a201017_r11 () (_ BitVec 64))
(declare-fun a201017_r12 () (_ BitVec 64))
(declare-fun a201017_r13 () (_ BitVec 64))
(declare-fun a201017_r14 () (_ BitVec 64))
(declare-fun a201017_r15 () (_ BitVec 64))
(declare-fun a201017_cf () Bool)
(declare-fun a201017_pf () Bool)
(declare-fun a201017_af () Bool)
(declare-fun a201017_zf () Bool)
(declare-fun a201017_sf () Bool)
(declare-fun a201017_tf () Bool)
(declare-fun a201017_if () Bool)
(define-fun a201017_df () Bool false)
(declare-fun a201017_of () Bool)
(declare-fun a201017_ie () Bool)
(declare-fun a201017_de () Bool)
(declare-fun a201017_ze () Bool)
(declare-fun a201017_oe () Bool)
(declare-fun a201017_ue () Bool)
(declare-fun a201017_pe () Bool)
(declare-fun a201017_ef () Bool)
(declare-fun a201017_es () Bool)
(declare-fun a201017_c0 () Bool)
(declare-fun a201017_c1 () Bool)
(declare-fun a201017_c2 () Bool)
(declare-fun a201017_RESERVED_STATUS_11 () Bool)
(declare-fun a201017_RESERVED_STATUS_12 () Bool)
(declare-fun a201017_RESERVED_STATUS_13 () Bool)
(declare-fun a201017_c3 () Bool)
(declare-fun a201017_RESERVED_STATUS_15 () Bool)
(define-fun a201017_x87top () (_ BitVec 3) (_ bv7 3))
(declare-fun a201017_tag0 () (_ BitVec 2))
(declare-fun a201017_tag1 () (_ BitVec 2))
(declare-fun a201017_tag2 () (_ BitVec 2))
(declare-fun a201017_tag3 () (_ BitVec 2))
(declare-fun a201017_tag4 () (_ BitVec 2))
(declare-fun a201017_tag5 () (_ BitVec 2))
(declare-fun a201017_tag6 () (_ BitVec 2))
(declare-fun a201017_tag7 () (_ BitVec 2))
(declare-fun a201017_mm0 () (_ BitVec 80))
(declare-fun a201017_mm1 () (_ BitVec 80))
(declare-fun a201017_mm2 () (_ BitVec 80))
(declare-fun a201017_mm3 () (_ BitVec 80))
(declare-fun a201017_mm4 () (_ BitVec 80))
(declare-fun a201017_mm5 () (_ BitVec 80))
(declare-fun a201017_mm6 () (_ BitVec 80))
(declare-fun a201017_mm7 () (_ BitVec 80))
(declare-fun a201017_zmm0 () (_ BitVec 512))
(declare-fun a201017_zmm1 () (_ BitVec 512))
(declare-fun a201017_zmm2 () (_ BitVec 512))
(declare-fun a201017_zmm3 () (_ BitVec 512))
(declare-fun a201017_zmm4 () (_ BitVec 512))
(declare-fun a201017_zmm5 () (_ BitVec 512))
(declare-fun a201017_zmm6 () (_ BitVec 512))
(declare-fun a201017_zmm7 () (_ BitVec 512))
(declare-fun a201017_zmm8 () (_ BitVec 512))
(declare-fun a201017_zmm9 () (_ BitVec 512))
(declare-fun a201017_zmm10 () (_ BitVec 512))
(declare-fun a201017_zmm11 () (_ BitVec 512))
(declare-fun a201017_zmm12 () (_ BitVec 512))
(declare-fun a201017_zmm13 () (_ BitVec 512))
(declare-fun a201017_zmm14 () (_ BitVec 512))
(declare-fun a201017_zmm15 () (_ BitVec 512))
(declare-fun a201017_zmm16 () (_ BitVec 512))
(declare-fun a201017_zmm17 () (_ BitVec 512))
(declare-fun a201017_zmm18 () (_ BitVec 512))
(declare-fun a201017_zmm19 () (_ BitVec 512))
(declare-fun a201017_zmm20 () (_ BitVec 512))
(declare-fun a201017_zmm21 () (_ BitVec 512))
(declare-fun a201017_zmm22 () (_ BitVec 512))
(declare-fun a201017_zmm23 () (_ BitVec 512))
(declare-fun a201017_zmm24 () (_ BitVec 512))
(declare-fun a201017_zmm25 () (_ BitVec 512))
(declare-fun a201017_zmm26 () (_ BitVec 512))
(declare-fun a201017_zmm27 () (_ BitVec 512))
(declare-fun a201017_zmm28 () (_ BitVec 512))
(declare-fun a201017_zmm29 () (_ BitVec 512))
(declare-fun a201017_zmm30 () (_ BitVec 512))
(declare-fun a201017_zmm31 () (_ BitVec 512))
(declare-const x86mem_0 (Array (_ BitVec 64) (_ BitVec 8)))
(define-fun return_addr () (_ BitVec 64) (mem_readbv64 x86mem_0 fnstart_rsp))
(define-fun llvm_arg0 () (_ BitVec 64) fnstart_rdi)
(declare-const llvm_t4 (_ BitVec 64))
(assert (= llvm_t4 a201017_rdi))
(assert (= llvm_t4 (mem_readbv64 x86mem_0 (bvsub fnstart_rsp (_ bv24 64)))))
(assert (= a201017_rbx fnstart_rbx))
(assert (= a201017_rsp (bvsub fnstart_rsp (_ bv40 64))))
(assert (= a201017_rbp (bvsub fnstart_rsp (_ bv8 64))))
(assert (= a201017_r12 fnstart_r12))
(assert (= a201017_r13 fnstart_r13))
(assert (= a201017_r14 fnstart_r14))
(assert (= a201017_r15 fnstart_r15))
(assert (= a201017_rdi (mem_readbv64 x86mem_0 (bvsub fnstart_rsp (_ bv24 64)))))
(assert (= (mem_readbv64 x86mem_0 (bvsub fnstart_rsp (_ bv8 64))) fnstart_rbp))
; LLVM: br label %block_0_201058
(define-fun x86local_0 () (_ BitVec 64) (bvadd a201017_rbp (_ bv18446744073709551600 64)))
(assert (on_stack x86local_0 (_ bv8 64)))
(define-fun x86local_1 () (_ BitVec 64) (mem_readbv64 x86mem_0 x86local_0))
(define-fun x86local_2 () (_ BitVec 64) (bvadd a201017_rbp (_ bv18446744073709551608 64)))
(assert (mc_only_stack_range x86local_2 (_ bv8 64)))
(define-fun x86mem_1 () (Array (_ BitVec 64) (_ BitVec 8)) (mem_writebv64 x86mem_0 x86local_2 x86local_1))
(assert (= #x0000000000201058 #x0000000000201058))
(assert (= (_ bv7 3) (_ bv7 3)))
(assert (= false false))
(assert (= llvm_t4 (mem_readbv64 x86mem_1 (bvsub fnstart_rsp (_ bv16 64)))))
(assert (= a201017_rbx fnstart_rbx))
(assert (= a201017_rsp (bvsub fnstart_rsp (_ bv40 64))))
(assert (= a201017_rbp (bvsub fnstart_rsp (_ bv8 64))))
(assert (= a201017_r12 fnstart_r12))
(check-sat-assuming ((not (= a201017_r13 fnstart_r13))))
(exit)
