def popw1 : instruction :=
  definst "popw" $ do
    pattern fun (v_2955 : Mem) => do
      v_15434 <- getRegister rsp;
      setRegister rsp (add v_15434 (expression.bv_nat 64 2));
      v_15437 <- evaluateAddress v_2955;
      v_15438 <- load v_15434 2;
      store v_15437 v_15438 2;
      pure ()
    pat_end
