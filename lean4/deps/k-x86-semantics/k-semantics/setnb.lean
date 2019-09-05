def setnb1 : instruction :=
  definst "setnb" $ do
    pattern fun (v_2583 : reg (bv 8)) => do
      v_4098 <- getRegister cf;
      setRegister (lhs.of_reg v_2583) (mux (notBool_ (eq v_4098 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2575 : Mem) => do
      v_8543 <- evaluateAddress v_2575;
      v_8544 <- getRegister cf;
      store v_8543 (mux (notBool_ (eq v_8544 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
