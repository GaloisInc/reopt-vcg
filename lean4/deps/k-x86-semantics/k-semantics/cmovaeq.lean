def cmovaeq1 : instruction :=
  definst "cmovaeq" $ do
    pattern fun (v_2447 : reg (bv 64)) (v_2448 : reg (bv 64)) => do
      v_4101 <- getRegister cf;
      v_4104 <- getRegister v_2447;
      v_4105 <- getRegister v_2448;
      setRegister (lhs.of_reg v_2448) (mux (notBool_ (eq v_4101 (expression.bv_nat 1 1))) v_4104 v_4105);
      pure ()
    pat_end;
    pattern fun (v_2442 : Mem) (v_2443 : reg (bv 64)) => do
      v_7794 <- getRegister cf;
      v_7797 <- evaluateAddress v_2442;
      v_7798 <- load v_7797 8;
      v_7799 <- getRegister v_2443;
      setRegister (lhs.of_reg v_2443) (mux (notBool_ (eq v_7794 (expression.bv_nat 1 1))) v_7798 v_7799);
      pure ()
    pat_end
