def setnc1 : instruction :=
  definst "setnc" $ do
    pattern fun (v_2632 : reg (bv 8)) => do
      v_4110 <- getRegister cf;
      setRegister (lhs.of_reg v_2632) (mux (notBool_ v_4110) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2625 : Mem) => do
      v_7974 <- evaluateAddress v_2625;
      v_7975 <- getRegister cf;
      store v_7974 (mux (notBool_ v_7975) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
