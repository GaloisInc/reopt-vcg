def cmovnll1 : instruction :=
  definst "cmovnll" $ do
    pattern fun (v_3052 : reg (bv 32)) (v_3053 : reg (bv 32)) => do
      v_4808 <- getRegister sf;
      v_4809 <- getRegister of;
      v_4811 <- getRegister v_3052;
      v_4812 <- getRegister v_3053;
      setRegister (lhs.of_reg v_3053) (mux (eq v_4808 v_4809) v_4811 v_4812);
      pure ()
    pat_end;
    pattern fun (v_3045 : Mem) (v_3048 : reg (bv 32)) => do
      v_8123 <- getRegister sf;
      v_8124 <- getRegister of;
      v_8126 <- evaluateAddress v_3045;
      v_8127 <- load v_8126 4;
      v_8128 <- getRegister v_3048;
      setRegister (lhs.of_reg v_3048) (mux (eq v_8123 v_8124) v_8127 v_8128);
      pure ()
    pat_end
