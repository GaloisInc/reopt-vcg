def cmovbeq1 : instruction :=
  definst "cmovbeq" $ do
    pattern fun (v_2454 : reg (bv 64)) (v_2455 : reg (bv 64)) => do
      v_4127 <- getRegister cf;
      v_4129 <- getRegister zf;
      v_4132 <- getRegister v_2454;
      v_4133 <- getRegister v_2455;
      setRegister (lhs.of_reg v_2455) (mux (bit_or (eq v_4127 (expression.bv_nat 1 1)) (eq v_4129 (expression.bv_nat 1 1))) v_4132 v_4133);
      pure ()
    pat_end;
    pattern fun (v_2445 : Mem) (v_2446 : reg (bv 64)) => do
      v_7872 <- getRegister cf;
      v_7874 <- getRegister zf;
      v_7877 <- evaluateAddress v_2445;
      v_7878 <- load v_7877 8;
      v_7879 <- getRegister v_2446;
      setRegister (lhs.of_reg v_2446) (mux (bit_or (eq v_7872 (expression.bv_nat 1 1)) (eq v_7874 (expression.bv_nat 1 1))) v_7878 v_7879);
      pure ()
    pat_end
