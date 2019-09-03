def cmovgew1 : instruction :=
  definst "cmovgew" $ do
    pattern fun (v_2602 : reg (bv 16)) (v_2603 : reg (bv 16)) => do
      v_4289 <- getRegister sf;
      v_4291 <- getRegister of;
      v_4294 <- getRegister v_2602;
      v_4295 <- getRegister v_2603;
      setRegister (lhs.of_reg v_2603) (mux (eq (eq v_4289 (expression.bv_nat 1 1)) (eq v_4291 (expression.bv_nat 1 1))) v_4294 v_4295);
      pure ()
    pat_end;
    pattern fun (v_2595 : Mem) (v_2594 : reg (bv 16)) => do
      v_7979 <- getRegister sf;
      v_7981 <- getRegister of;
      v_7984 <- evaluateAddress v_2595;
      v_7985 <- load v_7984 2;
      v_7986 <- getRegister v_2594;
      setRegister (lhs.of_reg v_2594) (mux (eq (eq v_7979 (expression.bv_nat 1 1)) (eq v_7981 (expression.bv_nat 1 1))) v_7985 v_7986);
      pure ()
    pat_end
