def cmovnbew1 : instruction :=
  definst "cmovnbew" $ do
    pattern fun (v_2802 : reg (bv 16)) (v_2803 : reg (bv 16)) => do
      v_4573 <- getRegister cf;
      v_4576 <- getRegister zf;
      v_4580 <- getRegister v_2802;
      v_4581 <- getRegister v_2803;
      setRegister (lhs.of_reg v_2803) (mux (bit_and (notBool_ (eq v_4573 (expression.bv_nat 1 1))) (notBool_ (eq v_4576 (expression.bv_nat 1 1)))) v_4580 v_4581);
      pure ()
    pat_end;
    pattern fun (v_2796 : Mem) (v_2798 : reg (bv 16)) => do
      v_8157 <- getRegister cf;
      v_8160 <- getRegister zf;
      v_8164 <- evaluateAddress v_2796;
      v_8165 <- load v_8164 2;
      v_8166 <- getRegister v_2798;
      setRegister (lhs.of_reg v_2798) (mux (bit_and (notBool_ (eq v_8157 (expression.bv_nat 1 1))) (notBool_ (eq v_8160 (expression.bv_nat 1 1)))) v_8165 v_8166);
      pure ()
    pat_end
