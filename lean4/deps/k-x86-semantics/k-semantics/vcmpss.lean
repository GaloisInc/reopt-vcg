def vcmpss : instruction :=
  definst "vcmpss" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister (lhs.of_reg xmm_2);
      (v_5 : expression (bv 96)) <- eval (extract v_4 0 96);
      (v_6 : expression (bv 32)) <- eval (extract v_4 96 128);
      v_7 <- evaluateAddress mem_1;
      v_8 <- load v_7 4;
      setRegister (lhs.of_reg xmm_3) (concat v_5 (mux (eq (/- (_,_,_) -/ cmp_single_pred v_6 v_8 (handleImmediateWithSignExtend imm_0 8 8)) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister (lhs.of_reg xmm_2);
      (v_5 : expression (bv 96)) <- eval (extract v_4 0 96);
      (v_6 : expression (bv 32)) <- eval (extract v_4 96 128);
      v_7 <- getRegister (lhs.of_reg xmm_1);
      (v_8 : expression (bv 32)) <- eval (extract v_7 96 128);
      setRegister (lhs.of_reg xmm_3) (concat v_5 (mux (eq (/- (_,_,_) -/ cmp_single_pred v_6 v_8 (handleImmediateWithSignExtend imm_0 8 8)) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)));
      pure ()
    pat_end
