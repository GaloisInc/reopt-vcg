def setl1 : instruction :=
  definst "setl" $ do
    pattern fun (v_2566 : reg (bv 8)) => do
      v_4028 <- getRegister sf;
      v_4029 <- getRegister of;
      setRegister (lhs.of_reg v_2566) (mux (notBool_ (eq v_4028 v_4029)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2559 : Mem) => do
      v_7935 <- evaluateAddress v_2559;
      v_7936 <- getRegister sf;
      v_7937 <- getRegister of;
      store v_7935 (mux (notBool_ (eq v_7936 v_7937)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
