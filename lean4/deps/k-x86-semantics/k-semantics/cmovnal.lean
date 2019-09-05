def cmovnal1 : instruction :=
  definst "cmovnal" $ do
    pattern fun (v_2809 : reg (bv 32)) (v_2810 : reg (bv 32)) => do
      v_4555 <- getRegister cf;
      v_4557 <- getRegister zf;
      v_4560 <- getRegister v_2809;
      v_4561 <- getRegister v_2810;
      setRegister (lhs.of_reg v_2810) (mux (bit_or (eq v_4555 (expression.bv_nat 1 1)) (eq v_4557 (expression.bv_nat 1 1))) v_4560 v_4561);
      pure ()
    pat_end;
    pattern fun (v_2802 : Mem) (v_2805 : reg (bv 32)) => do
      v_8116 <- getRegister cf;
      v_8118 <- getRegister zf;
      v_8121 <- evaluateAddress v_2802;
      v_8122 <- load v_8121 4;
      v_8123 <- getRegister v_2805;
      setRegister (lhs.of_reg v_2805) (mux (bit_or (eq v_8116 (expression.bv_nat 1 1)) (eq v_8118 (expression.bv_nat 1 1))) v_8122 v_8123);
      pure ()
    pat_end
