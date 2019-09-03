def cmovaeq1 : instruction :=
  definst "cmovaeq" $ do
    pattern fun (v_2395 : reg (bv 64)) (v_2396 : reg (bv 64)) => do
      v_4050 <- getRegister cf;
      v_4053 <- getRegister v_2395;
      v_4054 <- getRegister v_2396;
      setRegister (lhs.of_reg v_2396) (mux (notBool_ (eq v_4050 (expression.bv_nat 1 1))) v_4053 v_4054);
      pure ()
    pat_end;
    pattern fun (v_2391 : Mem) (v_2392 : reg (bv 64)) => do
      v_7781 <- getRegister cf;
      v_7784 <- evaluateAddress v_2391;
      v_7785 <- load v_7784 8;
      v_7786 <- getRegister v_2392;
      setRegister (lhs.of_reg v_2392) (mux (notBool_ (eq v_7781 (expression.bv_nat 1 1))) v_7785 v_7786);
      pure ()
    pat_end
