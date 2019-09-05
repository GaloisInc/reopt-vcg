def cmovnll1 : instruction :=
  definst "cmovnll" $ do
    pattern fun (v_3025 : reg (bv 32)) (v_3026 : reg (bv 32)) => do
      v_4882 <- getRegister sf;
      v_4884 <- getRegister of;
      v_4887 <- getRegister v_3025;
      v_4888 <- getRegister v_3026;
      setRegister (lhs.of_reg v_3026) (mux (eq (eq v_4882 (expression.bv_nat 1 1)) (eq v_4884 (expression.bv_nat 1 1))) v_4887 v_4888);
      pure ()
    pat_end;
    pattern fun (v_3018 : Mem) (v_3021 : reg (bv 32)) => do
      v_8371 <- getRegister sf;
      v_8373 <- getRegister of;
      v_8376 <- evaluateAddress v_3018;
      v_8377 <- load v_8376 4;
      v_8378 <- getRegister v_3021;
      setRegister (lhs.of_reg v_3021) (mux (eq (eq v_8371 (expression.bv_nat 1 1)) (eq v_8373 (expression.bv_nat 1 1))) v_8377 v_8378);
      pure ()
    pat_end
