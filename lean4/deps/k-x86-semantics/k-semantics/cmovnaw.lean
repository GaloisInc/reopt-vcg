def cmovnaw1 : instruction :=
  definst "cmovnaw" $ do
    pattern fun (v_2761 : reg (bv 16)) (v_2762 : reg (bv 16)) => do
      v_4517 <- getRegister cf;
      v_4519 <- getRegister zf;
      v_4522 <- getRegister v_2761;
      v_4523 <- getRegister v_2762;
      setRegister (lhs.of_reg v_2762) (mux (bit_or (eq v_4517 (expression.bv_nat 1 1)) (eq v_4519 (expression.bv_nat 1 1))) v_4522 v_4523);
      pure ()
    pat_end;
    pattern fun (v_2758 : Mem) (v_2757 : reg (bv 16)) => do
      v_8150 <- getRegister cf;
      v_8152 <- getRegister zf;
      v_8155 <- evaluateAddress v_2758;
      v_8156 <- load v_8155 2;
      v_8157 <- getRegister v_2757;
      setRegister (lhs.of_reg v_2757) (mux (bit_or (eq v_8150 (expression.bv_nat 1 1)) (eq v_8152 (expression.bv_nat 1 1))) v_8156 v_8157);
      pure ()
    pat_end
