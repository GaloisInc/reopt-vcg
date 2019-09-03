def popw1 : instruction :=
  definst "popw" $ do
    pattern fun (v_2878 : Mem) => do
      v_15761 <- getRegister rsp;
      setRegister rsp (add v_15761 (expression.bv_nat 64 2));
      v_15764 <- evaluateAddress v_2878;
      v_15765 <- load v_15761 2;
      store v_15764 v_15765 2;
      pure ()
    pat_end
