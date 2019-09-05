def cmovgeq1 : instruction :=
  definst "cmovgeq" $ do
    pattern fun (v_2649 : reg (bv 64)) (v_2650 : reg (bv 64)) => do
      v_4335 <- getRegister sf;
      v_4337 <- getRegister of;
      v_4340 <- getRegister v_2649;
      v_4341 <- getRegister v_2650;
      setRegister (lhs.of_reg v_2650) (mux (eq (eq v_4335 (expression.bv_nat 1 1)) (eq v_4337 (expression.bv_nat 1 1))) v_4340 v_4341);
      pure ()
    pat_end;
    pattern fun (v_2640 : Mem) (v_2641 : reg (bv 64)) => do
      v_7954 <- getRegister sf;
      v_7956 <- getRegister of;
      v_7959 <- evaluateAddress v_2640;
      v_7960 <- load v_7959 8;
      v_7961 <- getRegister v_2641;
      setRegister (lhs.of_reg v_2641) (mux (eq (eq v_7954 (expression.bv_nat 1 1)) (eq v_7956 (expression.bv_nat 1 1))) v_7960 v_7961);
      pure ()
    pat_end
