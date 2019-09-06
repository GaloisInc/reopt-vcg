def sete1 : instruction :=
  definst "sete" $ do
    pattern fun (v_2533 : reg (bv 8)) => do
      v_3984 <- getRegister zf;
      setRegister (lhs.of_reg v_2533) (mux v_3984 (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2526 : Mem) => do
      v_7916 <- evaluateAddress v_2526;
      v_7917 <- getRegister zf;
      store v_7916 (mux v_7917 (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
