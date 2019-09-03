def cmovnsw1 : instruction :=
  definst "cmovnsw" $ do
    pattern fun (v_3082 : reg (bv 16)) (v_3083 : reg (bv 16)) => do
      v_4960 <- getRegister sf;
      v_4963 <- getRegister v_3082;
      v_4964 <- getRegister v_3083;
      setRegister (lhs.of_reg v_3083) (mux (notBool_ (eq v_4960 (expression.bv_nat 1 1))) v_4963 v_4964);
      pure ()
    pat_end;
    pattern fun (v_3075 : Mem) (v_3074 : reg (bv 16)) => do
      v_8482 <- getRegister sf;
      v_8485 <- evaluateAddress v_3075;
      v_8486 <- load v_8485 2;
      v_8487 <- getRegister v_3074;
      setRegister (lhs.of_reg v_3074) (mux (notBool_ (eq v_8482 (expression.bv_nat 1 1))) v_8486 v_8487);
      pure ()
    pat_end
