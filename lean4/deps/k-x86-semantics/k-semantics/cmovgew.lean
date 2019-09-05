def cmovgew1 : instruction :=
  definst "cmovgew" $ do
    pattern fun (v_2666 : reg (bv 16)) (v_2667 : reg (bv 16)) => do
      v_4353 <- getRegister sf;
      v_4355 <- getRegister of;
      v_4358 <- getRegister v_2666;
      v_4359 <- getRegister v_2667;
      setRegister (lhs.of_reg v_2667) (mux (eq (eq v_4353 (expression.bv_nat 1 1)) (eq v_4355 (expression.bv_nat 1 1))) v_4358 v_4359);
      pure ()
    pat_end;
    pattern fun (v_2657 : Mem) (v_2658 : reg (bv 16)) => do
      v_7965 <- getRegister sf;
      v_7967 <- getRegister of;
      v_7970 <- evaluateAddress v_2657;
      v_7971 <- load v_7970 2;
      v_7972 <- getRegister v_2658;
      setRegister (lhs.of_reg v_2658) (mux (eq (eq v_7965 (expression.bv_nat 1 1)) (eq v_7967 (expression.bv_nat 1 1))) v_7971 v_7972);
      pure ()
    pat_end
