def setnz1 : instruction :=
  definst "setnz" $ do
    pattern fun (v_2649 : reg (bv 8)) => do
      v_4227 <- getRegister zf;
      setRegister (lhs.of_reg v_2649) (mux (notBool_ (eq v_4227 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2645 : Mem) => do
      v_9607 <- evaluateAddress v_2645;
      v_9608 <- getRegister zf;
      store v_9607 (mux (notBool_ (eq v_9608 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
