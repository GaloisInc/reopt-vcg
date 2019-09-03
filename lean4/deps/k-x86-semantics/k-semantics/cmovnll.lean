def cmovnll1 : instruction :=
  definst "cmovnll" $ do
    pattern fun (v_2959 : reg (bv 32)) (v_2960 : reg (bv 32)) => do
      v_4818 <- getRegister sf;
      v_4820 <- getRegister of;
      v_4823 <- getRegister v_2959;
      v_4824 <- getRegister v_2960;
      setRegister (lhs.of_reg v_2960) (mux (eq (eq v_4818 (expression.bv_nat 1 1)) (eq v_4820 (expression.bv_nat 1 1))) v_4823 v_4824);
      pure ()
    pat_end;
    pattern fun (v_2955 : Mem) (v_2956 : reg (bv 32)) => do
      v_8385 <- getRegister sf;
      v_8387 <- getRegister of;
      v_8390 <- evaluateAddress v_2955;
      v_8391 <- load v_8390 4;
      v_8392 <- getRegister v_2956;
      setRegister (lhs.of_reg v_2956) (mux (eq (eq v_8385 (expression.bv_nat 1 1)) (eq v_8387 (expression.bv_nat 1 1))) v_8391 v_8392);
      pure ()
    pat_end
