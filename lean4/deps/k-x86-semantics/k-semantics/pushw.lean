def pushw : instruction :=
  definst "pushw" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- getRegister rsp;
      v_2 <- eval (sub v_1 (expression.bv_nat 64 2));
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 2;
      store v_2 v_4 2;
      setRegister rsp v_2;
      pure ()
    pat_end
