def cmovnol1 : instruction :=
  definst "cmovnol" $ do
    pattern fun (v_2998 : reg (bv 32)) (v_2999 : reg (bv 32)) => do
      v_4870 <- getRegister of;
      v_4873 <- getRegister v_2998;
      v_4874 <- getRegister v_2999;
      setRegister (lhs.of_reg v_2999) (mux (notBool_ (eq v_4870 (expression.bv_nat 1 1))) v_4873 v_4874);
      pure ()
    pat_end;
    pattern fun (v_2994 : Mem) (v_2995 : reg (bv 32)) => do
      v_8388 <- getRegister of;
      v_8391 <- evaluateAddress v_2994;
      v_8392 <- load v_8391 4;
      v_8393 <- getRegister v_2995;
      setRegister (lhs.of_reg v_2995) (mux (notBool_ (eq v_8388 (expression.bv_nat 1 1))) v_8392 v_8393);
      pure ()
    pat_end
