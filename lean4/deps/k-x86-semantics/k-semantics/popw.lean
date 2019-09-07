def popw1 : instruction :=
  definst "popw" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- getRegister rsp;
      setRegister rsp (add v_1 (expression.bv_nat 64 2));
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_1 2;
      store v_3 v_4 2;
      pure ()
    pat_end
