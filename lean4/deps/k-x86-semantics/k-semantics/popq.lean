def popq1 : instruction :=
  definst "popq" $ do
    pattern fun (v_2951 : Mem) => do
      v_15428 <- getRegister rsp;
      setRegister rsp (add v_15428 (expression.bv_nat 64 8));
      v_15431 <- evaluateAddress v_2951;
      v_15432 <- load v_15428 8;
      store v_15431 v_15432 8;
      pure ()
    pat_end
