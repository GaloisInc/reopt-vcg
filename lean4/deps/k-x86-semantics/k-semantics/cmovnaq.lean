def cmovnaq1 : instruction :=
  definst "cmovnaq" $ do
    pattern fun (v_2816 : reg (bv 64)) (v_2817 : reg (bv 64)) => do
      v_4568 <- getRegister cf;
      v_4570 <- getRegister zf;
      v_4573 <- getRegister v_2816;
      v_4574 <- getRegister v_2817;
      setRegister (lhs.of_reg v_2817) (mux (bit_or (eq v_4568 (expression.bv_nat 1 1)) (eq v_4570 (expression.bv_nat 1 1))) v_4573 v_4574);
      pure ()
    pat_end;
    pattern fun (v_2811 : Mem) (v_2812 : reg (bv 64)) => do
      v_8126 <- getRegister cf;
      v_8128 <- getRegister zf;
      v_8131 <- evaluateAddress v_2811;
      v_8132 <- load v_8131 8;
      v_8133 <- getRegister v_2812;
      setRegister (lhs.of_reg v_2812) (mux (bit_or (eq v_8126 (expression.bv_nat 1 1)) (eq v_8128 (expression.bv_nat 1 1))) v_8132 v_8133);
      pure ()
    pat_end
