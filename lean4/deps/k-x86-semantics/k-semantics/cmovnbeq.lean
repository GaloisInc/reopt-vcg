def cmovnbeq1 : instruction :=
  definst "cmovnbeq" $ do
    pattern fun (v_2780 : reg (bv 64)) (v_2781 : reg (bv 64)) => do
      v_4545 <- getRegister cf;
      v_4548 <- getRegister zf;
      v_4552 <- getRegister v_2780;
      v_4553 <- getRegister v_2781;
      setRegister (lhs.of_reg v_2781) (mux (bit_and (notBool_ (eq v_4545 (expression.bv_nat 1 1))) (notBool_ (eq v_4548 (expression.bv_nat 1 1)))) v_4552 v_4553);
      pure ()
    pat_end;
    pattern fun (v_2775 : Mem) (v_2776 : reg (bv 64)) => do
      v_8172 <- getRegister cf;
      v_8175 <- getRegister zf;
      v_8179 <- evaluateAddress v_2775;
      v_8180 <- load v_8179 8;
      v_8181 <- getRegister v_2776;
      setRegister (lhs.of_reg v_2776) (mux (bit_and (notBool_ (eq v_8172 (expression.bv_nat 1 1))) (notBool_ (eq v_8175 (expression.bv_nat 1 1)))) v_8180 v_8181);
      pure ()
    pat_end
