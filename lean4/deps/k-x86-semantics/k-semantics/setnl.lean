def setnl1 : instruction :=
  definst "setnl" $ do
    pattern fun (v_2676 : reg (bv 8)) => do
      v_4167 <- getRegister sf;
      v_4168 <- getRegister of;
      setRegister (lhs.of_reg v_2676) (mux (eq v_4167 v_4168) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2669 : Mem) => do
      v_8000 <- evaluateAddress v_2669;
      v_8001 <- getRegister sf;
      v_8002 <- getRegister of;
      store v_8000 (mux (eq v_8001 v_8002) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
