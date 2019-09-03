def pushw1 : instruction :=
  definst "pushw" $ do
    pattern fun (v_3236 : Mem) => do
      v_16114 <- getRegister rsp;
      v_16115 <- eval (sub v_16114 (expression.bv_nat 64 2));
      v_16116 <- evaluateAddress v_3236;
      v_16117 <- load v_16116 2;
      store v_16115 (mi 16 (svalueMInt v_16117)) 2;
      setRegister rsp v_16115;
      pure ()
    pat_end
