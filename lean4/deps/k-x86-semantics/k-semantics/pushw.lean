def pushw1 : instruction :=
  definst "pushw" $ do
    pattern fun (v_3328 : Mem) => do
      v_15266 <- getRegister rsp;
      v_15267 <- eval (sub v_15266 (expression.bv_nat 64 2));
      v_15268 <- evaluateAddress v_3328;
      v_15269 <- load v_15268 2;
      store v_15267 v_15269 2;
      setRegister rsp v_15267;
      pure ()
    pat_end
