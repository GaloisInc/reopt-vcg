def cmovnlq1 : instruction :=
  definst "cmovnlq" $ do
    pattern fun (v_2980 : reg (bv 64)) (v_2981 : reg (bv 64)) => do
      v_4844 <- getRegister sf;
      v_4846 <- getRegister of;
      v_4849 <- getRegister v_2980;
      v_4850 <- getRegister v_2981;
      setRegister (lhs.of_reg v_2981) (mux (eq (eq v_4844 (expression.bv_nat 1 1)) (eq v_4846 (expression.bv_nat 1 1))) v_4849 v_4850);
      pure ()
    pat_end;
    pattern fun (v_2976 : Mem) (v_2977 : reg (bv 64)) => do
      v_8368 <- getRegister sf;
      v_8370 <- getRegister of;
      v_8373 <- evaluateAddress v_2976;
      v_8374 <- load v_8373 8;
      v_8375 <- getRegister v_2977;
      setRegister (lhs.of_reg v_2977) (mux (eq (eq v_8368 (expression.bv_nat 1 1)) (eq v_8370 (expression.bv_nat 1 1))) v_8374 v_8375);
      pure ()
    pat_end
