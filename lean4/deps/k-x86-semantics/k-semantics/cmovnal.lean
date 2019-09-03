def cmovnal1 : instruction :=
  definst "cmovnal" $ do
    pattern fun (v_2743 : reg (bv 32)) (v_2744 : reg (bv 32)) => do
      v_4491 <- getRegister cf;
      v_4493 <- getRegister zf;
      v_4496 <- getRegister v_2743;
      v_4497 <- getRegister v_2744;
      setRegister (lhs.of_reg v_2744) (mux (bit_or (eq v_4491 (expression.bv_nat 1 1)) (eq v_4493 (expression.bv_nat 1 1))) v_4496 v_4497);
      pure ()
    pat_end;
    pattern fun (v_2739 : Mem) (v_2740 : reg (bv 32)) => do
      v_8130 <- getRegister cf;
      v_8132 <- getRegister zf;
      v_8135 <- evaluateAddress v_2739;
      v_8136 <- load v_8135 4;
      v_8137 <- getRegister v_2740;
      setRegister (lhs.of_reg v_2740) (mux (bit_or (eq v_8130 (expression.bv_nat 1 1)) (eq v_8132 (expression.bv_nat 1 1))) v_8136 v_8137);
      pure ()
    pat_end
