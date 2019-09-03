def cmovgew1 : instruction :=
  definst "cmovgew" $ do
    pattern fun (v_2616 : reg (bv 16)) (v_2617 : reg (bv 16)) => do
      v_4302 <- getRegister sf;
      v_4304 <- getRegister of;
      v_4307 <- getRegister v_2616;
      v_4308 <- getRegister v_2617;
      setRegister (lhs.of_reg v_2617) (mux (eq (eq v_4302 (expression.bv_nat 1 1)) (eq v_4304 (expression.bv_nat 1 1))) v_4307 v_4308);
      pure ()
    pat_end;
    pattern fun (v_2606 : Mem) (v_2608 : reg (bv 16)) => do
      v_7952 <- getRegister sf;
      v_7954 <- getRegister of;
      v_7957 <- evaluateAddress v_2606;
      v_7958 <- load v_7957 2;
      v_7959 <- getRegister v_2608;
      setRegister (lhs.of_reg v_2608) (mux (eq (eq v_7952 (expression.bv_nat 1 1)) (eq v_7954 (expression.bv_nat 1 1))) v_7958 v_7959);
      pure ()
    pat_end
