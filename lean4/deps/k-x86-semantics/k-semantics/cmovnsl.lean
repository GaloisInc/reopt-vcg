def cmovnsl1 : instruction :=
  definst "cmovnsl" $ do
    pattern fun (v_3060 : reg (bv 32)) (v_3061 : reg (bv 32)) => do
      v_4941 <- getRegister sf;
      v_4944 <- getRegister v_3060;
      v_4945 <- getRegister v_3061;
      setRegister (lhs.of_reg v_3061) (mux (notBool_ (eq v_4941 (expression.bv_nat 1 1))) v_4944 v_4945);
      pure ()
    pat_end;
    pattern fun (v_3052 : Mem) (v_3053 : reg (bv 32)) => do
      v_8437 <- getRegister sf;
      v_8440 <- evaluateAddress v_3052;
      v_8441 <- load v_8440 4;
      v_8442 <- getRegister v_3053;
      setRegister (lhs.of_reg v_3053) (mux (notBool_ (eq v_8437 (expression.bv_nat 1 1))) v_8441 v_8442);
      pure ()
    pat_end
