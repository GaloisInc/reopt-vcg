def popw1 : instruction :=
  definst "popw" $ do
    pattern fun (v_2864 : Mem) => do
      v_16376 <- getRegister rsp;
      setRegister rsp (add v_16376 (expression.bv_nat 64 2));
      v_16379 <- evaluateAddress v_2864;
      v_16380 <- load v_16376 2;
      store v_16379 v_16380 2;
      pure ()
    pat_end
