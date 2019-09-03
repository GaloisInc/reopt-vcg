def cmovge1 : instruction :=
  definst "cmovge" $ do
    pattern fun (v_2557 : Mem) (v_2556 : reg (bv 32)) => do
      v_9051 <- getRegister sf;
      v_9053 <- getRegister of;
      v_9056 <- evaluateAddress v_2557;
      v_9057 <- load v_9056 4;
      v_9058 <- getRegister v_2556;
      setRegister (lhs.of_reg v_2556) (mux (eq (eq v_9051 (expression.bv_nat 1 1)) (eq v_9053 (expression.bv_nat 1 1))) v_9057 v_9058);
      pure ()
    pat_end;
    pattern fun (v_2573 : Mem) (v_2574 : reg (bv 64)) => do
      v_9061 <- getRegister sf;
      v_9063 <- getRegister of;
      v_9066 <- evaluateAddress v_2573;
      v_9067 <- load v_9066 8;
      v_9068 <- getRegister v_2574;
      setRegister (lhs.of_reg v_2574) (mux (eq (eq v_9061 (expression.bv_nat 1 1)) (eq v_9063 (expression.bv_nat 1 1))) v_9067 v_9068);
      pure ()
    pat_end;
    pattern fun (v_2591 : Mem) (v_2590 : reg (bv 16)) => do
      v_9071 <- getRegister sf;
      v_9073 <- getRegister of;
      v_9076 <- evaluateAddress v_2591;
      v_9077 <- load v_9076 2;
      v_9078 <- getRegister v_2590;
      setRegister (lhs.of_reg v_2590) (mux (eq (eq v_9071 (expression.bv_nat 1 1)) (eq v_9073 (expression.bv_nat 1 1))) v_9077 v_9078);
      pure ()
    pat_end
