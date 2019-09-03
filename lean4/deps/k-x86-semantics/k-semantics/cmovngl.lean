def cmovngl1 : instruction :=
  definst "cmovngl" $ do
    pattern fun (v_2905 : reg (bv 32)) (v_2906 : reg (bv 32)) => do
      v_4716 <- getRegister zf;
      v_4718 <- getRegister sf;
      v_4720 <- getRegister of;
      v_4725 <- getRegister v_2905;
      v_4726 <- getRegister v_2906;
      setRegister (lhs.of_reg v_2906) (mux (bit_or (eq v_4716 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_4718 (expression.bv_nat 1 1)) (eq v_4720 (expression.bv_nat 1 1))))) v_4725 v_4726);
      pure ()
    pat_end;
    pattern fun (v_2901 : Mem) (v_2902 : reg (bv 32)) => do
      v_8301 <- getRegister zf;
      v_8303 <- getRegister sf;
      v_8305 <- getRegister of;
      v_8310 <- evaluateAddress v_2901;
      v_8311 <- load v_8310 4;
      v_8312 <- getRegister v_2902;
      setRegister (lhs.of_reg v_2902) (mux (bit_or (eq v_8301 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_8303 (expression.bv_nat 1 1)) (eq v_8305 (expression.bv_nat 1 1))))) v_8311 v_8312);
      pure ()
    pat_end
