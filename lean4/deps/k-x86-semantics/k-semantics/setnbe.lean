def setnbe1 : instruction :=
  definst "setnbe" $ do
    pattern fun (v_2539 : reg (bv 8)) => do
      v_4055 <- getRegister cf;
      v_4058 <- getRegister zf;
      setRegister (lhs.of_reg v_2539) (mux (bit_and (notBool_ (eq v_4055 (expression.bv_nat 1 1))) (notBool_ (eq v_4058 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2535 : Mem) => do
      v_9526 <- evaluateAddress v_2535;
      v_9527 <- getRegister cf;
      v_9530 <- getRegister zf;
      store v_9526 (mux (bit_and (notBool_ (eq v_9527 (expression.bv_nat 1 1))) (notBool_ (eq v_9530 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
