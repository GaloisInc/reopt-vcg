def setc1 : instruction :=
  definst "setc" $ do
    pattern fun (v_2522 : reg (bv 8)) => do
      v_3975 <- getRegister cf;
      setRegister (lhs.of_reg v_2522) (mux v_3975 (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2515 : Mem) => do
      v_7912 <- evaluateAddress v_2515;
      v_7913 <- getRegister cf;
      store v_7912 (mux v_7913 (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
