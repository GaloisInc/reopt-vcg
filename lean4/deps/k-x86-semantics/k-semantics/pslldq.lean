def pslldq : instruction :=
  definst "pslldq" $ do
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      (v_4 : expression (bv 128)) <- eval (extract (shl (mux (ugt v_3 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_3)) (expression.bv_nat 128 3)) 0 128);
      (v_5 : expression (bv 128)) <- eval (extract (shl v_2 v_4) 0 128);
      setRegister (lhs.of_reg xmm_1) v_5;
      pure ()
    pat_end
