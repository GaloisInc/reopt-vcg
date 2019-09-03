def cmovaq1 : instruction :=
  definst "cmovaq" $ do
    pattern fun (v_2411 : reg (bv 64)) (v_2412 : reg (bv 64)) => do
      v_4074 <- getRegister cf;
      v_4077 <- getRegister zf;
      v_4081 <- getRegister v_2411;
      v_4082 <- getRegister v_2412;
      setRegister (lhs.of_reg v_2412) (mux (bit_and (notBool_ (eq v_4074 (expression.bv_nat 1 1))) (notBool_ (eq v_4077 (expression.bv_nat 1 1)))) v_4081 v_4082);
      pure ()
    pat_end;
    pattern fun (v_2406 : Mem) (v_2407 : reg (bv 64)) => do
      v_7836 <- getRegister cf;
      v_7839 <- getRegister zf;
      v_7843 <- evaluateAddress v_2406;
      v_7844 <- load v_7843 8;
      v_7845 <- getRegister v_2407;
      setRegister (lhs.of_reg v_2407) (mux (bit_and (notBool_ (eq v_7836 (expression.bv_nat 1 1))) (notBool_ (eq v_7839 (expression.bv_nat 1 1)))) v_7844 v_7845);
      pure ()
    pat_end
