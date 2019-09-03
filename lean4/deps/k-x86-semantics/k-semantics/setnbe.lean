def setnbe1 : instruction :=
  definst "setnbe" $ do
    pattern fun (v_2526 : reg (bv 8)) => do
      v_4042 <- getRegister cf;
      v_4045 <- getRegister zf;
      setRegister (lhs.of_reg v_2526) (mux (bit_and (notBool_ (eq v_4042 (expression.bv_nat 1 1))) (notBool_ (eq v_4045 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2522 : Mem) => do
      v_9502 <- evaluateAddress v_2522;
      v_9503 <- getRegister cf;
      v_9506 <- getRegister zf;
      store v_9502 (mux (bit_and (notBool_ (eq v_9503 (expression.bv_nat 1 1))) (notBool_ (eq v_9506 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
