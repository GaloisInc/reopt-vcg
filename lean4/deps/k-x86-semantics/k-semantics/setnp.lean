def setnp1 : instruction :=
  definst "setnp" $ do
    pattern fun (v_2627 : reg (bv 8)) => do
      v_4201 <- getRegister pf;
      setRegister (lhs.of_reg v_2627) (mux (notBool_ (eq v_4201 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2623 : Mem) => do
      v_9595 <- evaluateAddress v_2623;
      v_9596 <- getRegister pf;
      store v_9595 (mux (notBool_ (eq v_9596 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
