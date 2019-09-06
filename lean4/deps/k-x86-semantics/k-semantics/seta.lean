def seta1 : instruction :=
  definst "seta" $ do
    pattern fun (v_2478 : reg (bv 8)) => do
      v_3929 <- getRegister cf;
      v_3931 <- getRegister zf;
      setRegister (lhs.of_reg v_2478) (mux (bit_and (notBool_ v_3929) (notBool_ v_3931)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2471 : Mem) => do
      v_7889 <- evaluateAddress v_2471;
      v_7890 <- getRegister cf;
      v_7892 <- getRegister zf;
      store v_7889 (mux (bit_and (notBool_ v_7890) (notBool_ v_7892)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
