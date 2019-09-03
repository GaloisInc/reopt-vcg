def pushw1 : instruction :=
  definst "pushw" $ do
    pattern fun (v_3251 : Mem) => do
      v_15495 <- getRegister rsp;
      v_15496 <- eval (sub v_15495 (expression.bv_nat 64 2));
      v_15497 <- evaluateAddress v_3251;
      v_15498 <- load v_15497 2;
      store v_15496 (mi 16 (svalueMInt v_15498)) 2;
      setRegister rsp v_15496;
      pure ()
    pat_end
