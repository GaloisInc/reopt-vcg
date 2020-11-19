def vcmpsd : instruction :=
  definst "vcmpsd" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister (lhs.of_reg xmm_2);
      (v_5 : expression (bv 64)) <- eval (extract v_4 0 64);
      (v_6 : expression (bv 64)) <- eval (extract v_4 64 128);
      v_7 <- evaluateAddress mem_1;
      v_8 <- load v_7 8;
      setRegister (lhs.of_reg xmm_3) (concat v_5 (mux (eq (/- (_,_,_) -/ cmp_double_pred v_6 v_8 (handleImmediateWithSignExtend imm_0 8 8)) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister (lhs.of_reg xmm_2);
      (v_5 : expression (bv 64)) <- eval (extract v_4 0 64);
      (v_6 : expression (bv 64)) <- eval (extract v_4 64 128);
      v_7 <- getRegister (lhs.of_reg xmm_1);
      (v_8 : expression (bv 64)) <- eval (extract v_7 64 128);
      setRegister (lhs.of_reg xmm_3) (concat v_5 (mux (eq (/- (_,_,_) -/ cmp_double_pred v_6 v_8 (handleImmediateWithSignExtend imm_0 8 8)) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end
