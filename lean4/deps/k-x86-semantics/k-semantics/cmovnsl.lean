def cmovnsl1 : instruction :=
  definst "cmovnsl" $ do
    pattern fun (v_3048 : reg (bv 32)) (v_3049 : reg (bv 32)) => do
      v_4928 <- getRegister sf;
      v_4931 <- getRegister v_3048;
      v_4932 <- getRegister v_3049;
      setRegister (lhs.of_reg v_3049) (mux (notBool_ (eq v_4928 (expression.bv_nat 1 1))) v_4931 v_4932);
      pure ()
    pat_end;
    pattern fun (v_3040 : Mem) (v_3041 : reg (bv 32)) => do
      v_8464 <- getRegister sf;
      v_8467 <- evaluateAddress v_3040;
      v_8468 <- load v_8467 4;
      v_8469 <- getRegister v_3041;
      setRegister (lhs.of_reg v_3041) (mux (notBool_ (eq v_8464 (expression.bv_nat 1 1))) v_8468 v_8469);
      pure ()
    pat_end
