def cmovnol1 : instruction :=
  definst "cmovnol" $ do
    pattern fun (v_2986 : reg (bv 32)) (v_2987 : reg (bv 32)) => do
      v_4857 <- getRegister of;
      v_4860 <- getRegister v_2986;
      v_4861 <- getRegister v_2987;
      setRegister (lhs.of_reg v_2987) (mux (notBool_ (eq v_4857 (expression.bv_nat 1 1))) v_4860 v_4861);
      pure ()
    pat_end;
    pattern fun (v_2982 : Mem) (v_2983 : reg (bv 32)) => do
      v_8415 <- getRegister of;
      v_8418 <- evaluateAddress v_2982;
      v_8419 <- load v_8418 4;
      v_8420 <- getRegister v_2983;
      setRegister (lhs.of_reg v_2983) (mux (notBool_ (eq v_8415 (expression.bv_nat 1 1))) v_8419 v_8420);
      pure ()
    pat_end
