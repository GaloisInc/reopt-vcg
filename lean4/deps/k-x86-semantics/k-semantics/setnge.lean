def setnge1 : instruction :=
  definst "setnge" $ do
    pattern fun (v_2665 : reg (bv 8)) => do
      v_4153 <- getRegister sf;
      v_4154 <- getRegister of;
      setRegister (lhs.of_reg v_2665) (mux (notBool_ (eq v_4153 v_4154)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2658 : Mem) => do
      v_7993 <- evaluateAddress v_2658;
      v_7994 <- getRegister sf;
      v_7995 <- getRegister of;
      store v_7993 (mux (notBool_ (eq v_7994 v_7995)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
