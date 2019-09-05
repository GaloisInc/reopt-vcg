def setnae1 : instruction :=
  definst "setnae" $ do
    pattern fun (v_2572 : reg (bv 8)) => do
      v_4086 <- getRegister cf;
      setRegister (lhs.of_reg v_2572) (mux (eq v_4086 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2564 : Mem) => do
      v_8538 <- evaluateAddress v_2564;
      v_8539 <- getRegister cf;
      store v_8538 (mux (eq v_8539 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
