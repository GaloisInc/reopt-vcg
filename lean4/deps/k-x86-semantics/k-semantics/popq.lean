def popq1 : instruction :=
  definst "popq" $ do
    pattern fun (v_2874 : Mem) => do
      v_15755 <- getRegister rsp;
      setRegister rsp (add v_15755 (expression.bv_nat 64 8));
      v_15758 <- evaluateAddress v_2874;
      v_15759 <- load v_15755 8;
      store v_15758 v_15759 8;
      pure ()
    pat_end
