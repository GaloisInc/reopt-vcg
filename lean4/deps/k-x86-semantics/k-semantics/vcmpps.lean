def vcmpps : instruction :=
  definst "vcmpps" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister (lhs.of_reg xmm_2);
      v_5 <- evaluateAddress mem_1;
      v_6 <- load v_5 16;
      v_7 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      setRegister (lhs.of_reg xmm_3) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_4 0 32) (extract v_6 0 32) v_7) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_4 32 64) (extract v_6 32 64) v_7) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_4 64 96) (extract v_6 64 96) v_7) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_4 96 128) (extract v_6 96 128) v_7) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- getRegister (lhs.of_reg ymm_2);
      v_5 <- evaluateAddress mem_1;
      v_6 <- load v_5 32;
      v_7 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      setRegister (lhs.of_reg ymm_3) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_4 0 32) (extract v_6 0 32) v_7) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_4 32 64) (extract v_6 32 64) v_7) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_4 64 96) (extract v_6 64 96) v_7) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_4 96 128) (extract v_6 96 128) v_7) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_4 128 160) (extract v_6 128 160) v_7) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_4 160 192) (extract v_6 160 192) v_7) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_4 192 224) (extract v_6 192 224) v_7) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_4 224 256) (extract v_6 224 256) v_7) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister (lhs.of_reg xmm_2);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      v_6 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      setRegister (lhs.of_reg xmm_3) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_4 0 32) (extract v_5 0 32) v_6) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_4 32 64) (extract v_5 32 64) v_6) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_4 64 96) (extract v_5 64 96) v_6) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_4 96 128) (extract v_5 96 128) v_6) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- getRegister (lhs.of_reg ymm_2);
      v_5 <- getRegister (lhs.of_reg ymm_1);
      v_6 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      setRegister (lhs.of_reg ymm_3) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_4 0 32) (extract v_5 0 32) v_6) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_4 32 64) (extract v_5 32 64) v_6) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_4 64 96) (extract v_5 64 96) v_6) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_4 96 128) (extract v_5 96 128) v_6) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_4 128 160) (extract v_5 128 160) v_6) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_4 160 192) (extract v_5 160 192) v_6) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_4 192 224) (extract v_5 192 224) v_6) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_4 224 256) (extract v_5 224 256) v_6) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end
