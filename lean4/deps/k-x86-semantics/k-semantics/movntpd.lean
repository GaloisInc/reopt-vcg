def movntpd1 : instruction :=
  definst "movntpd" $ do
    pattern fun (v_2639 : reg (bv 128)) (v_2638 : Mem) => do
      v_8495 <- evaluateAddress v_2638;
      v_8496 <- getRegister v_2639;
      store v_8495 v_8496 16;
      pure ()
    pat_end
