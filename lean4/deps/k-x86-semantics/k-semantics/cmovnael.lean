def cmovnael1 : instruction :=
  definst "cmovnael" $ do
    pattern fun (v_2782 : reg (bv 32)) (v_2783 : reg (bv 32)) => do
      v_4525 <- getRegister cf;
      v_4527 <- getRegister v_2782;
      v_4528 <- getRegister v_2783;
      setRegister (lhs.of_reg v_2783) (mux (eq v_4525 (expression.bv_nat 1 1)) v_4527 v_4528);
      pure ()
    pat_end;
    pattern fun (v_2775 : Mem) (v_2778 : reg (bv 32)) => do
      v_8095 <- getRegister cf;
      v_8097 <- evaluateAddress v_2775;
      v_8098 <- load v_8097 4;
      v_8099 <- getRegister v_2778;
      setRegister (lhs.of_reg v_2778) (mux (eq v_8095 (expression.bv_nat 1 1)) v_8098 v_8099);
      pure ()
    pat_end
