def cmovnaq1 : instruction :=
  definst "cmovnaq" $ do
    pattern fun (v_2764 : reg (bv 64)) (v_2765 : reg (bv 64)) => do
      v_4517 <- getRegister cf;
      v_4519 <- getRegister zf;
      v_4522 <- getRegister v_2764;
      v_4523 <- getRegister v_2765;
      setRegister (lhs.of_reg v_2765) (mux (bit_or (eq v_4517 (expression.bv_nat 1 1)) (eq v_4519 (expression.bv_nat 1 1))) v_4522 v_4523);
      pure ()
    pat_end;
    pattern fun (v_2760 : Mem) (v_2761 : reg (bv 64)) => do
      v_8113 <- getRegister cf;
      v_8115 <- getRegister zf;
      v_8118 <- evaluateAddress v_2760;
      v_8119 <- load v_8118 8;
      v_8120 <- getRegister v_2761;
      setRegister (lhs.of_reg v_2761) (mux (bit_or (eq v_8113 (expression.bv_nat 1 1)) (eq v_8115 (expression.bv_nat 1 1))) v_8119 v_8120);
      pure ()
    pat_end
