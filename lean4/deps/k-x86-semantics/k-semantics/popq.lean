def popq1 : instruction :=
  definst "popq" $ do
    pattern fun (v_2860 : Mem) => do
      v_16370 <- getRegister rsp;
      setRegister rsp (add v_16370 (expression.bv_nat 64 8));
      v_16373 <- evaluateAddress v_2860;
      v_16374 <- load v_16370 8;
      store v_16373 v_16374 8;
      pure ()
    pat_end
