def cmpps : instruction :=
  definst "cmpps" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      v_4 <- evaluateAddress mem_1;
      v_5 <- load v_4 16;
      v_6 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      setRegister (lhs.of_reg xmm_2) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_3 0 32) (extract v_5 0 32) v_6) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_3 32 64) (extract v_5 32 64) v_6) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_3 64 96) (extract v_5 64 96) v_6) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_3 96 128) (extract v_5 96 128) v_6) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      v_5 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      setRegister (lhs.of_reg xmm_2) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_3 0 32) (extract v_4 0 32) v_5) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_3 32 64) (extract v_4 32 64) v_5) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_3 64 96) (extract v_4 64 96) v_5) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (/- (_,_,_) -/ cmp_single_pred (extract v_3 96 128) (extract v_4 96 128) v_5) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end
