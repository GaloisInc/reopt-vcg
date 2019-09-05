def cmovbel1 : instruction :=
  definst "cmovbel" $ do
    pattern fun (v_2502 : reg (bv 32)) (v_2503 : reg (bv 32)) => do
      v_4173 <- getRegister cf;
      v_4175 <- getRegister zf;
      v_4178 <- getRegister v_2502;
      v_4179 <- getRegister v_2503;
      setRegister (lhs.of_reg v_2503) (mux (bit_or (eq v_4173 (expression.bv_nat 1 1)) (eq v_4175 (expression.bv_nat 1 1))) v_4178 v_4179);
      pure ()
    pat_end;
    pattern fun (v_2491 : Mem) (v_2494 : reg (bv 32)) => do
      v_7847 <- getRegister cf;
      v_7849 <- getRegister zf;
      v_7852 <- evaluateAddress v_2491;
      v_7853 <- load v_7852 4;
      v_7854 <- getRegister v_2494;
      setRegister (lhs.of_reg v_2494) (mux (bit_or (eq v_7847 (expression.bv_nat 1 1)) (eq v_7849 (expression.bv_nat 1 1))) v_7853 v_7854);
      pure ()
    pat_end
