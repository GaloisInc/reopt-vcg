def cmovbeq1 : instruction :=
  definst "cmovbeq" $ do
    pattern fun (v_2517 : reg (bv 64)) (v_2518 : reg (bv 64)) => do
      v_4191 <- getRegister cf;
      v_4193 <- getRegister zf;
      v_4196 <- getRegister v_2517;
      v_4197 <- getRegister v_2518;
      setRegister (lhs.of_reg v_2518) (mux (bit_or (eq v_4191 (expression.bv_nat 1 1)) (eq v_4193 (expression.bv_nat 1 1))) v_4196 v_4197);
      pure ()
    pat_end;
    pattern fun (v_2508 : Mem) (v_2509 : reg (bv 64)) => do
      v_7858 <- getRegister cf;
      v_7860 <- getRegister zf;
      v_7863 <- evaluateAddress v_2508;
      v_7864 <- load v_7863 8;
      v_7865 <- getRegister v_2509;
      setRegister (lhs.of_reg v_2509) (mux (bit_or (eq v_7858 (expression.bv_nat 1 1)) (eq v_7860 (expression.bv_nat 1 1))) v_7864 v_7865);
      pure ()
    pat_end
