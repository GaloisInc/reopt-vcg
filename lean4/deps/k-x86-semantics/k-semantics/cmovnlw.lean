def cmovnlw1 : instruction :=
  definst "cmovnlw" $ do
    pattern fun (v_2991 : reg (bv 16)) (v_2992 : reg (bv 16)) => do
      v_4857 <- getRegister sf;
      v_4859 <- getRegister of;
      v_4862 <- getRegister v_2991;
      v_4863 <- getRegister v_2992;
      setRegister (lhs.of_reg v_2992) (mux (eq (eq v_4857 (expression.bv_nat 1 1)) (eq v_4859 (expression.bv_nat 1 1))) v_4862 v_4863);
      pure ()
    pat_end;
    pattern fun (v_2985 : Mem) (v_2987 : reg (bv 16)) => do
      v_8378 <- getRegister sf;
      v_8380 <- getRegister of;
      v_8383 <- evaluateAddress v_2985;
      v_8384 <- load v_8383 2;
      v_8385 <- getRegister v_2987;
      setRegister (lhs.of_reg v_2987) (mux (eq (eq v_8378 (expression.bv_nat 1 1)) (eq v_8380 (expression.bv_nat 1 1))) v_8384 v_8385);
      pure ()
    pat_end
