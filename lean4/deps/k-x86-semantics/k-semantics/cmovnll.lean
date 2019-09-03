def cmovnll1 : instruction :=
  definst "cmovnll" $ do
    pattern fun (v_2971 : reg (bv 32)) (v_2972 : reg (bv 32)) => do
      v_4831 <- getRegister sf;
      v_4833 <- getRegister of;
      v_4836 <- getRegister v_2971;
      v_4837 <- getRegister v_2972;
      setRegister (lhs.of_reg v_2972) (mux (eq (eq v_4831 (expression.bv_nat 1 1)) (eq v_4833 (expression.bv_nat 1 1))) v_4836 v_4837);
      pure ()
    pat_end;
    pattern fun (v_2967 : Mem) (v_2968 : reg (bv 32)) => do
      v_8358 <- getRegister sf;
      v_8360 <- getRegister of;
      v_8363 <- evaluateAddress v_2967;
      v_8364 <- load v_8363 4;
      v_8365 <- getRegister v_2968;
      setRegister (lhs.of_reg v_2968) (mux (eq (eq v_8358 (expression.bv_nat 1 1)) (eq v_8360 (expression.bv_nat 1 1))) v_8364 v_8365);
      pure ()
    pat_end
