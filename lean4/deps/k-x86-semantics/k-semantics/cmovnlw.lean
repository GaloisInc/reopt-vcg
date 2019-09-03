def cmovnlw1 : instruction :=
  definst "cmovnlw" $ do
    pattern fun (v_2977 : reg (bv 16)) (v_2978 : reg (bv 16)) => do
      v_4844 <- getRegister sf;
      v_4846 <- getRegister of;
      v_4849 <- getRegister v_2977;
      v_4850 <- getRegister v_2978;
      setRegister (lhs.of_reg v_2978) (mux (eq (eq v_4844 (expression.bv_nat 1 1)) (eq v_4846 (expression.bv_nat 1 1))) v_4849 v_4850);
      pure ()
    pat_end;
    pattern fun (v_2974 : Mem) (v_2973 : reg (bv 16)) => do
      v_8405 <- getRegister sf;
      v_8407 <- getRegister of;
      v_8410 <- evaluateAddress v_2974;
      v_8411 <- load v_8410 2;
      v_8412 <- getRegister v_2973;
      setRegister (lhs.of_reg v_2973) (mux (eq (eq v_8405 (expression.bv_nat 1 1)) (eq v_8407 (expression.bv_nat 1 1))) v_8411 v_8412);
      pure ()
    pat_end
