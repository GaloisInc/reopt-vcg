def setge1 : instruction :=
  definst "setge" $ do
    pattern fun (v_2555 : reg (bv 8)) => do
      v_4014 <- getRegister sf;
      v_4015 <- getRegister of;
      setRegister (lhs.of_reg v_2555) (mux (eq v_4014 v_4015) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2548 : Mem) => do
      v_7929 <- evaluateAddress v_2548;
      v_7930 <- getRegister sf;
      v_7931 <- getRegister of;
      store v_7929 (mux (eq v_7930 v_7931) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
