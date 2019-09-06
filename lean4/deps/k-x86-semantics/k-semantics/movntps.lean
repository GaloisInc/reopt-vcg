def movntps1 : instruction :=
  definst "movntps" $ do
    pattern fun (v_2643 : reg (bv 128)) (v_2642 : Mem) => do
      v_8498 <- evaluateAddress v_2642;
      v_8499 <- getRegister v_2643;
      store v_8498 v_8499 16;
      pure ()
    pat_end
