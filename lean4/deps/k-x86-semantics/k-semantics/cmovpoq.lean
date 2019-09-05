def cmovpoq1 : instruction :=
  definst "cmovpoq" $ do
    pattern fun (v_3254 : reg (bv 64)) (v_3255 : reg (bv 64)) => do
      v_5149 <- getRegister pf;
      v_5152 <- getRegister v_3254;
      v_5153 <- getRegister v_3255;
      setRegister (lhs.of_reg v_3255) (mux (notBool_ (eq v_5149 (expression.bv_nat 1 1))) v_5152 v_5153);
      pure ()
    pat_end;
    pattern fun (v_3249 : Mem) (v_3250 : reg (bv 64)) => do
      v_8557 <- getRegister pf;
      v_8560 <- evaluateAddress v_3249;
      v_8561 <- load v_8560 8;
      v_8562 <- getRegister v_3250;
      setRegister (lhs.of_reg v_3250) (mux (notBool_ (eq v_8557 (expression.bv_nat 1 1))) v_8561 v_8562);
      pure ()
    pat_end
