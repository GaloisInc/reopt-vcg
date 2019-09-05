def pushw1 : instruction :=
  definst "pushw" $ do
    pattern fun (v_3300 : Mem) => do
      v_15290 <- getRegister rsp;
      v_15291 <- eval (sub v_15290 (expression.bv_nat 64 2));
      v_15292 <- evaluateAddress v_3300;
      v_15293 <- load v_15292 2;
      store v_15291 v_15293 2;
      setRegister rsp v_15291;
      pure ()
    pat_end
