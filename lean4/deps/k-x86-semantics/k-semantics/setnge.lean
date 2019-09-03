def setnge1 : instruction :=
  definst "setnge" $ do
    pattern fun (v_2570 : reg (bv 8)) => do
      v_4114 <- getRegister sf;
      v_4116 <- getRegister of;
      setRegister (lhs.of_reg v_2570) (mux (notBool_ (eq (eq v_4114 (expression.bv_nat 1 1)) (eq v_4116 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2566 : Mem) => do
      v_9536 <- evaluateAddress v_2566;
      v_9537 <- getRegister sf;
      v_9539 <- getRegister of;
      store v_9536 (mux (notBool_ (eq (eq v_9537 (expression.bv_nat 1 1)) (eq v_9539 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
