def setnbe1 : instruction :=
  definst "setnbe" $ do
    pattern fun (v_2594 : reg (bv 8)) => do
      v_4115 <- getRegister cf;
      v_4118 <- getRegister zf;
      setRegister (lhs.of_reg v_2594) (mux (bit_and (notBool_ (eq v_4115 (expression.bv_nat 1 1))) (notBool_ (eq v_4118 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2586 : Mem) => do
      v_8549 <- evaluateAddress v_2586;
      v_8550 <- getRegister cf;
      v_8553 <- getRegister zf;
      store v_8549 (mux (bit_and (notBool_ (eq v_8550 (expression.bv_nat 1 1))) (notBool_ (eq v_8553 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
