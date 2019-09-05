def cmovnpl1 : instruction :=
  definst "cmovnpl" $ do
    pattern fun (v_3079 : reg (bv 32)) (v_3080 : reg (bv 32)) => do
      v_4954 <- getRegister pf;
      v_4957 <- getRegister v_3079;
      v_4958 <- getRegister v_3080;
      setRegister (lhs.of_reg v_3080) (mux (notBool_ (eq v_4954 (expression.bv_nat 1 1))) v_4957 v_4958);
      pure ()
    pat_end;
    pattern fun (v_3072 : Mem) (v_3075 : reg (bv 32)) => do
      v_8425 <- getRegister pf;
      v_8428 <- evaluateAddress v_3072;
      v_8429 <- load v_8428 4;
      v_8430 <- getRegister v_3075;
      setRegister (lhs.of_reg v_3075) (mux (notBool_ (eq v_8425 (expression.bv_nat 1 1))) v_8429 v_8430);
      pure ()
    pat_end
