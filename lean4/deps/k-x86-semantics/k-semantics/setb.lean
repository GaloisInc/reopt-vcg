def setb1 : instruction :=
  definst "setb" $ do
    pattern fun (v_2473 : reg (bv 8)) => do
      v_3933 <- getRegister cf;
      setRegister (lhs.of_reg v_2473) (mux (eq v_3933 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2465 : Mem) => do
      v_8466 <- evaluateAddress v_2465;
      v_8467 <- getRegister cf;
      store v_8466 (mux (eq v_8467 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
