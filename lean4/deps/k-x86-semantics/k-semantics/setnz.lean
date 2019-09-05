def setnz1 : instruction :=
  definst "setnz" $ do
    pattern fun (v_2704 : reg (bv 8)) => do
      v_4283 <- getRegister zf;
      setRegister (lhs.of_reg v_2704) (mux (notBool_ (eq v_4283 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2696 : Mem) => do
      v_8630 <- evaluateAddress v_2696;
      v_8631 <- getRegister zf;
      store v_8630 (mux (notBool_ (eq v_8631 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
