def cmovgel1 : instruction :=
  definst "cmovgel" $ do
    pattern fun (v_2634 : reg (bv 32)) (v_2635 : reg (bv 32)) => do
      v_4317 <- getRegister sf;
      v_4319 <- getRegister of;
      v_4322 <- getRegister v_2634;
      v_4323 <- getRegister v_2635;
      setRegister (lhs.of_reg v_2635) (mux (eq (eq v_4317 (expression.bv_nat 1 1)) (eq v_4319 (expression.bv_nat 1 1))) v_4322 v_4323);
      pure ()
    pat_end;
    pattern fun (v_2623 : Mem) (v_2626 : reg (bv 32)) => do
      v_7943 <- getRegister sf;
      v_7945 <- getRegister of;
      v_7948 <- evaluateAddress v_2623;
      v_7949 <- load v_7948 4;
      v_7950 <- getRegister v_2626;
      setRegister (lhs.of_reg v_2626) (mux (eq (eq v_7943 (expression.bv_nat 1 1)) (eq v_7945 (expression.bv_nat 1 1))) v_7949 v_7950);
      pure ()
    pat_end
