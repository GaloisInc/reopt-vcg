def cmovael1 : instruction :=
  definst "cmovael" $ do
    pattern fun (v_3336 : reg (bv 32)) (v_3337 : reg (bv 32)) => do
      v_6817 <- getRegister cf;
      v_6820 <- getRegister v_3336;
      v_6821 <- getRegister v_3337;
      setRegister (lhs.of_reg v_3337) (mux (notBool_ (eq v_6817 (expression.bv_nat 1 1))) v_6820 v_6821);
      pure ()
    pat_end;
    pattern fun (v_3333 : Mem) (v_3332 : reg (bv 32)) => do
      v_9976 <- getRegister cf;
      v_9979 <- evaluateAddress v_3333;
      v_9980 <- load v_9979 4;
      v_9981 <- getRegister v_3332;
      setRegister (lhs.of_reg v_3332) (mux (notBool_ (eq v_9976 (expression.bv_nat 1 1))) v_9980 v_9981);
      pure ()
    pat_end
