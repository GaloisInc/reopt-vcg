def popq1 : instruction :=
  definst "popq" $ do
    pattern fun (v_2924 : Mem) => do
      v_15488 <- getRegister rsp;
      setRegister rsp (add v_15488 (expression.bv_nat 64 8));
      v_15491 <- evaluateAddress v_2924;
      v_15492 <- load v_15488 8;
      store v_15491 v_15492 8;
      pure ()
    pat_end
