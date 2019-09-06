def setno1 : instruction :=
  definst "setno" $ do
    pattern fun (v_2698 : reg (bv 8)) => do
      v_4198 <- getRegister of;
      setRegister (lhs.of_reg v_2698) (mux (notBool_ v_4198) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2691 : Mem) => do
      v_8015 <- evaluateAddress v_2691;
      v_8016 <- getRegister of;
      store v_8015 (mux (notBool_ v_8016) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
