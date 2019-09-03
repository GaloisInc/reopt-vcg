def cmovnlq1 : instruction :=
  definst "cmovnlq" $ do
    pattern fun (v_2969 : reg (bv 64)) (v_2970 : reg (bv 64)) => do
      v_4831 <- getRegister sf;
      v_4833 <- getRegister of;
      v_4836 <- getRegister v_2969;
      v_4837 <- getRegister v_2970;
      setRegister (lhs.of_reg v_2970) (mux (eq (eq v_4831 (expression.bv_nat 1 1)) (eq v_4833 (expression.bv_nat 1 1))) v_4836 v_4837);
      pure ()
    pat_end;
    pattern fun (v_2964 : Mem) (v_2965 : reg (bv 64)) => do
      v_8395 <- getRegister sf;
      v_8397 <- getRegister of;
      v_8400 <- evaluateAddress v_2964;
      v_8401 <- load v_8400 8;
      v_8402 <- getRegister v_2965;
      setRegister (lhs.of_reg v_2965) (mux (eq (eq v_8395 (expression.bv_nat 1 1)) (eq v_8397 (expression.bv_nat 1 1))) v_8401 v_8402);
      pure ()
    pat_end
