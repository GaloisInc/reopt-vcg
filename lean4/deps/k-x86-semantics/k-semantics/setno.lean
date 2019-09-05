def setno1 : instruction :=
  definst "setno" $ do
    pattern fun (v_2671 : reg (bv 8)) => do
      v_4244 <- getRegister of;
      setRegister (lhs.of_reg v_2671) (mux (notBool_ (eq v_4244 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2663 : Mem) => do
      v_8612 <- evaluateAddress v_2663;
      v_8613 <- getRegister of;
      store v_8612 (mux (notBool_ (eq v_8613 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
