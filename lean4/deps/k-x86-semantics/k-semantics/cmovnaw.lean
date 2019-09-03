def cmovnaw1 : instruction :=
  definst "cmovnaw" $ do
    pattern fun (v_2775 : reg (bv 16)) (v_2776 : reg (bv 16)) => do
      v_4530 <- getRegister cf;
      v_4532 <- getRegister zf;
      v_4535 <- getRegister v_2775;
      v_4536 <- getRegister v_2776;
      setRegister (lhs.of_reg v_2776) (mux (bit_or (eq v_4530 (expression.bv_nat 1 1)) (eq v_4532 (expression.bv_nat 1 1))) v_4535 v_4536);
      pure ()
    pat_end;
    pattern fun (v_2769 : Mem) (v_2771 : reg (bv 16)) => do
      v_8123 <- getRegister cf;
      v_8125 <- getRegister zf;
      v_8128 <- evaluateAddress v_2769;
      v_8129 <- load v_8128 2;
      v_8130 <- getRegister v_2771;
      setRegister (lhs.of_reg v_2771) (mux (bit_or (eq v_8123 (expression.bv_nat 1 1)) (eq v_8125 (expression.bv_nat 1 1))) v_8129 v_8130);
      pure ()
    pat_end
