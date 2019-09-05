def setnc1 : instruction :=
  definst "setnc" $ do
    pattern fun (v_2605 : reg (bv 8)) => do
      v_4132 <- getRegister cf;
      setRegister (lhs.of_reg v_2605) (mux (notBool_ (eq v_4132 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2597 : Mem) => do
      v_8559 <- evaluateAddress v_2597;
      v_8560 <- getRegister cf;
      store v_8559 (mux (notBool_ (eq v_8560 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
