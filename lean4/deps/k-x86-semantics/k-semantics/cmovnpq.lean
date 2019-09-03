def cmovnpq1 : instruction :=
  definst "cmovnpq" $ do
    pattern fun (v_3034 : reg (bv 64)) (v_3035 : reg (bv 64)) => do
      v_4914 <- getRegister pf;
      v_4917 <- getRegister v_3034;
      v_4918 <- getRegister v_3035;
      setRegister (lhs.of_reg v_3035) (mux (notBool_ (eq v_4914 (expression.bv_nat 1 1))) v_4917 v_4918);
      pure ()
    pat_end;
    pattern fun (v_3030 : Mem) (v_3031 : reg (bv 64)) => do
      v_8420 <- getRegister pf;
      v_8423 <- evaluateAddress v_3030;
      v_8424 <- load v_8423 8;
      v_8425 <- getRegister v_3031;
      setRegister (lhs.of_reg v_3031) (mux (notBool_ (eq v_8420 (expression.bv_nat 1 1))) v_8424 v_8425);
      pure ()
    pat_end
