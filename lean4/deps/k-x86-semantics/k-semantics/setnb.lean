def setnb1 : instruction :=
  definst "setnb" $ do
    pattern fun (v_2528 : reg (bv 8)) => do
      v_4042 <- getRegister cf;
      setRegister (lhs.of_reg v_2528) (mux (notBool_ (eq v_4042 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2524 : Mem) => do
      v_9520 <- evaluateAddress v_2524;
      v_9521 <- getRegister cf;
      store v_9520 (mux (notBool_ (eq v_9521 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
