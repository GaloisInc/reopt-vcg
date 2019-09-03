def cmovnleq1 : instruction :=
  definst "cmovnleq" $ do
    pattern fun (v_2953 : reg (bv 64)) (v_2954 : reg (bv 64)) => do
      v_4797 <- getRegister zf;
      v_4800 <- getRegister sf;
      v_4802 <- getRegister of;
      v_4806 <- getRegister v_2953;
      v_4807 <- getRegister v_2954;
      setRegister (lhs.of_reg v_2954) (mux (bit_and (notBool_ (eq v_4797 (expression.bv_nat 1 1))) (eq (eq v_4800 (expression.bv_nat 1 1)) (eq v_4802 (expression.bv_nat 1 1)))) v_4806 v_4807);
      pure ()
    pat_end;
    pattern fun (v_2949 : Mem) (v_2950 : reg (bv 64)) => do
      v_8330 <- getRegister zf;
      v_8333 <- getRegister sf;
      v_8335 <- getRegister of;
      v_8339 <- evaluateAddress v_2949;
      v_8340 <- load v_8339 8;
      v_8341 <- getRegister v_2950;
      setRegister (lhs.of_reg v_2950) (mux (bit_and (notBool_ (eq v_8330 (expression.bv_nat 1 1))) (eq (eq v_8333 (expression.bv_nat 1 1)) (eq v_8335 (expression.bv_nat 1 1)))) v_8340 v_8341);
      pure ()
    pat_end
