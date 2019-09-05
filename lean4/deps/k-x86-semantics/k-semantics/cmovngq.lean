def cmovngq1 : instruction :=
  definst "cmovngq" $ do
    pattern fun (v_2978 : reg (bv 64)) (v_2979 : reg (bv 64)) => do
      v_4797 <- getRegister zf;
      v_4799 <- getRegister sf;
      v_4801 <- getRegister of;
      v_4806 <- getRegister v_2978;
      v_4807 <- getRegister v_2979;
      setRegister (lhs.of_reg v_2979) (mux (bit_or (eq v_4797 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_4799 (expression.bv_nat 1 1)) (eq v_4801 (expression.bv_nat 1 1))))) v_4806 v_4807);
      pure ()
    pat_end;
    pattern fun (v_2973 : Mem) (v_2974 : reg (bv 64)) => do
      v_8301 <- getRegister zf;
      v_8303 <- getRegister sf;
      v_8305 <- getRegister of;
      v_8310 <- evaluateAddress v_2973;
      v_8311 <- load v_8310 8;
      v_8312 <- getRegister v_2974;
      setRegister (lhs.of_reg v_2974) (mux (bit_or (eq v_8301 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_8303 (expression.bv_nat 1 1)) (eq v_8305 (expression.bv_nat 1 1))))) v_8311 v_8312);
      pure ()
    pat_end
