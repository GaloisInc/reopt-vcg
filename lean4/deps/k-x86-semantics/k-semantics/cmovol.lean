def cmovol1 : instruction :=
  definst "cmovol" $ do
    pattern fun (v_3118 : reg (bv 32)) (v_3119 : reg (bv 32)) => do
      v_5004 <- getRegister of;
      v_5006 <- getRegister v_3118;
      v_5007 <- getRegister v_3119;
      setRegister (lhs.of_reg v_3119) (mux (eq v_5004 (expression.bv_nat 1 1)) v_5006 v_5007);
      pure ()
    pat_end;
    pattern fun (v_3114 : Mem) (v_3115 : reg (bv 32)) => do
      v_8514 <- getRegister of;
      v_8516 <- evaluateAddress v_3114;
      v_8517 <- load v_8516 4;
      v_8518 <- getRegister v_3115;
      setRegister (lhs.of_reg v_3115) (mux (eq v_8514 (expression.bv_nat 1 1)) v_8517 v_8518);
      pure ()
    pat_end
