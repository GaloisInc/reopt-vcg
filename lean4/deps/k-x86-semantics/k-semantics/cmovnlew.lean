def cmovnlew1 : instruction :=
  definst "cmovnlew" $ do
    pattern fun (v_3014 : reg (bv 16)) (v_3015 : reg (bv 16)) => do
      v_4865 <- getRegister zf;
      v_4868 <- getRegister sf;
      v_4870 <- getRegister of;
      v_4874 <- getRegister v_3014;
      v_4875 <- getRegister v_3015;
      setRegister (lhs.of_reg v_3015) (mux (bit_and (notBool_ (eq v_4865 (expression.bv_nat 1 1))) (eq (eq v_4868 (expression.bv_nat 1 1)) (eq v_4870 (expression.bv_nat 1 1)))) v_4874 v_4875);
      pure ()
    pat_end;
    pattern fun (v_3009 : Mem) (v_3010 : reg (bv 16)) => do
      v_8357 <- getRegister zf;
      v_8360 <- getRegister sf;
      v_8362 <- getRegister of;
      v_8366 <- evaluateAddress v_3009;
      v_8367 <- load v_8366 2;
      v_8368 <- getRegister v_3010;
      setRegister (lhs.of_reg v_3010) (mux (bit_and (notBool_ (eq v_8357 (expression.bv_nat 1 1))) (eq (eq v_8360 (expression.bv_nat 1 1)) (eq v_8362 (expression.bv_nat 1 1)))) v_8367 v_8368);
      pure ()
    pat_end
