def popw1 : instruction :=
  definst "popw" $ do
    pattern fun (v_2928 : Mem) => do
      v_15494 <- getRegister rsp;
      setRegister rsp (add v_15494 (expression.bv_nat 64 2));
      v_15497 <- evaluateAddress v_2928;
      v_15498 <- load v_15494 2;
      store v_15497 v_15498 2;
      pure ()
    pat_end
