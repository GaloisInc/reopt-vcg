def setz1 : instruction :=
  definst "setz" $ do
    pattern fun (v_2797 : reg (bv 8)) => do
      v_4288 <- getRegister zf;
      setRegister (lhs.of_reg v_2797) (mux v_4288 (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2790 : Mem) => do
      v_8056 <- evaluateAddress v_2790;
      v_8057 <- getRegister zf;
      store v_8056 (mux v_8057 (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
