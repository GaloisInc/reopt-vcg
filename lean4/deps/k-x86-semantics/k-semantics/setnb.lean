def setnb1 : instruction :=
  definst "setnb" $ do
    pattern fun (v_2610 : reg (bv 8)) => do
      v_4082 <- getRegister cf;
      setRegister (lhs.of_reg v_2610) (mux (notBool_ v_4082) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2603 : Mem) => do
      v_7961 <- evaluateAddress v_2603;
      v_7962 <- getRegister cf;
      store v_7961 (mux (notBool_ v_7962) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
