def cmovbew1 : instruction :=
  definst "cmovbew" $ do
    pattern fun (v_2484 : reg (bv 16)) (v_2485 : reg (bv 16)) => do
      v_4158 <- getRegister cf;
      v_4160 <- getRegister zf;
      v_4163 <- getRegister v_2484;
      v_4164 <- getRegister v_2485;
      setRegister (lhs.of_reg v_2485) (mux (bit_or (eq v_4158 (expression.bv_nat 1 1)) (eq v_4160 (expression.bv_nat 1 1))) v_4163 v_4164);
      pure ()
    pat_end;
    pattern fun (v_2474 : Mem) (v_2476 : reg (bv 16)) => do
      v_7856 <- getRegister cf;
      v_7858 <- getRegister zf;
      v_7861 <- evaluateAddress v_2474;
      v_7862 <- load v_7861 2;
      v_7863 <- getRegister v_2476;
      setRegister (lhs.of_reg v_2476) (mux (bit_or (eq v_7856 (expression.bv_nat 1 1)) (eq v_7858 (expression.bv_nat 1 1))) v_7862 v_7863);
      pure ()
    pat_end
