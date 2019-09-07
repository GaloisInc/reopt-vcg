def popq1 : instruction :=
  definst "popq" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- getRegister rsp;
      setRegister rsp (add v_1 (expression.bv_nat 64 8));
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_1 8;
      store v_3 v_4 8;
      pure ()
    pat_end
