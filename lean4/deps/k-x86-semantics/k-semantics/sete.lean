def sete1 : instruction :=
  definst "sete" $ do
    pattern fun (v_2438 : reg (bv 8)) => do
      v_3904 <- getRegister zf;
      setRegister (lhs.of_reg v_2438) (mux (eq v_3904 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2434 : Mem) => do
      v_9437 <- evaluateAddress v_2434;
      v_9438 <- getRegister zf;
      store v_9437 (mux (eq v_9438 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
