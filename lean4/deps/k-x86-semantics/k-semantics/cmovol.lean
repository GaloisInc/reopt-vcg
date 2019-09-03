def cmovol1 : instruction :=
  definst "cmovol" $ do
    pattern fun (v_3130 : reg (bv 32)) (v_3131 : reg (bv 32)) => do
      v_5017 <- getRegister of;
      v_5019 <- getRegister v_3130;
      v_5020 <- getRegister v_3131;
      setRegister (lhs.of_reg v_3131) (mux (eq v_5017 (expression.bv_nat 1 1)) v_5019 v_5020);
      pure ()
    pat_end;
    pattern fun (v_3126 : Mem) (v_3127 : reg (bv 32)) => do
      v_8487 <- getRegister of;
      v_8489 <- evaluateAddress v_3126;
      v_8490 <- load v_8489 4;
      v_8491 <- getRegister v_3127;
      setRegister (lhs.of_reg v_3127) (mux (eq v_8487 (expression.bv_nat 1 1)) v_8490 v_8491);
      pure ()
    pat_end
