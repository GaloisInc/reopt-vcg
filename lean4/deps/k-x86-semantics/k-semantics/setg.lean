def setg : instruction :=
  definst "setg" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- getRegister zf;
      v_3 <- getRegister sf;
      v_4 <- getRegister of;
      store v_1 (mux (bit_and (notBool_ v_2) (eq v_3 v_4)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end;
    pattern fun (rh_0 : reg (bv 8)) => do
      v_1 <- getRegister zf;
      v_2 <- getRegister sf;
      v_3 <- getRegister of;
      setRegister (lhs.of_reg rh_0) (mux (bit_and (notBool_ v_1) (eq v_2 v_3)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end