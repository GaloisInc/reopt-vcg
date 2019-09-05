def movntps1 : instruction :=
  definst "movntps" $ do
    pattern fun (v_2617 : reg (bv 128)) (v_2616 : Mem) => do
      v_8471 <- evaluateAddress v_2616;
      v_8472 <- getRegister v_2617;
      store v_8471 v_8472 16;
      pure ()
    pat_end
