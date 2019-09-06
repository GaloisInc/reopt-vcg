def setg1 : instruction :=
  definst "setg" $ do
    pattern fun (v_2544 : reg (bv 8)) => do
      v_3998 <- getRegister zf;
      v_4000 <- getRegister sf;
      v_4001 <- getRegister of;
      setRegister (lhs.of_reg v_2544) (mux (bit_and (notBool_ v_3998) (eq v_4000 v_4001)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2537 : Mem) => do
      v_7920 <- evaluateAddress v_2537;
      v_7921 <- getRegister zf;
      v_7923 <- getRegister sf;
      v_7924 <- getRegister of;
      store v_7920 (mux (bit_and (notBool_ v_7921) (eq v_7923 v_7924)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
