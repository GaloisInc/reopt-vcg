def setnp1 : instruction :=
  definst "setnp" $ do
    pattern fun (v_2614 : reg (bv 8)) => do
      v_4188 <- getRegister pf;
      setRegister (lhs.of_reg v_2614) (mux (notBool_ (eq v_4188 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2610 : Mem) => do
      v_9571 <- evaluateAddress v_2610;
      v_9572 <- getRegister pf;
      store v_9571 (mux (notBool_ (eq v_9572 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
