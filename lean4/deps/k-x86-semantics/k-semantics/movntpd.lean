def movntpd1 : instruction :=
  definst "movntpd" $ do
    pattern fun (v_2563 : reg (bv 128)) (v_2562 : Mem) => do
      v_8604 <- evaluateAddress v_2562;
      v_8605 <- getRegister v_2563;
      store v_8604 v_8605 16;
      pure ()
    pat_end
