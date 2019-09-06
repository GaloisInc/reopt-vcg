def setna1 : instruction :=
  definst "setna" $ do
    pattern fun (v_2588 : reg (bv 8)) => do
      v_4061 <- getRegister cf;
      v_4062 <- getRegister zf;
      setRegister (lhs.of_reg v_2588) (mux (bit_or v_4061 v_4062) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2581 : Mem) => do
      v_7951 <- evaluateAddress v_2581;
      v_7952 <- getRegister cf;
      v_7953 <- getRegister zf;
      store v_7951 (mux (bit_or v_7952 v_7953) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
