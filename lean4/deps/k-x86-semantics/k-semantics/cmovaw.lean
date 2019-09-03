def cmovaw1 : instruction :=
  definst "cmovaw" $ do
    pattern fun (v_2433 : reg (bv 16)) (v_2434 : reg (bv 16)) => do
      v_4102 <- getRegister cf;
      v_4105 <- getRegister zf;
      v_4109 <- getRegister v_2433;
      v_4110 <- getRegister v_2434;
      setRegister (lhs.of_reg v_2434) (mux (bit_and (notBool_ (eq v_4102 (expression.bv_nat 1 1))) (notBool_ (eq v_4105 (expression.bv_nat 1 1)))) v_4109 v_4110);
      pure ()
    pat_end;
    pattern fun (v_2427 : Mem) (v_2429 : reg (bv 16)) => do
      v_7821 <- getRegister cf;
      v_7824 <- getRegister zf;
      v_7828 <- evaluateAddress v_2427;
      v_7829 <- load v_7828 2;
      v_7830 <- getRegister v_2429;
      setRegister (lhs.of_reg v_2429) (mux (bit_and (notBool_ (eq v_7821 (expression.bv_nat 1 1))) (notBool_ (eq v_7824 (expression.bv_nat 1 1)))) v_7829 v_7830);
      pure ()
    pat_end
