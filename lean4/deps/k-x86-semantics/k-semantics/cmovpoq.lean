def cmovpoq1 : instruction :=
  definst "cmovpoq" $ do
    pattern fun (v_3191 : reg (bv 64)) (v_3192 : reg (bv 64)) => do
      v_5085 <- getRegister pf;
      v_5088 <- getRegister v_3191;
      v_5089 <- getRegister v_3192;
      setRegister (lhs.of_reg v_3192) (mux (notBool_ (eq v_5085 (expression.bv_nat 1 1))) v_5088 v_5089);
      pure ()
    pat_end;
    pattern fun (v_3186 : Mem) (v_3187 : reg (bv 64)) => do
      v_8571 <- getRegister pf;
      v_8574 <- evaluateAddress v_3186;
      v_8575 <- load v_8574 8;
      v_8576 <- getRegister v_3187;
      setRegister (lhs.of_reg v_3187) (mux (notBool_ (eq v_8571 (expression.bv_nat 1 1))) v_8575 v_8576);
      pure ()
    pat_end
