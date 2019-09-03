def setnz1 : instruction :=
  definst "setnz" $ do
    pattern fun (v_2636 : reg (bv 8)) => do
      v_4214 <- getRegister zf;
      setRegister (lhs.of_reg v_2636) (mux (notBool_ (eq v_4214 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2632 : Mem) => do
      v_9583 <- evaluateAddress v_2632;
      v_9584 <- getRegister zf;
      store v_9583 (mux (notBool_ (eq v_9584 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
