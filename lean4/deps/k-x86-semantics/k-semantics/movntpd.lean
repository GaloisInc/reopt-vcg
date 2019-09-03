def movntpd1 : instruction :=
  definst "movntpd" $ do
    pattern fun (v_2550 : reg (bv 128)) (v_2549 : Mem) => do
      v_8624 <- evaluateAddress v_2549;
      v_8625 <- getRegister v_2550;
      store v_8624 v_8625 16;
      pure ()
    pat_end
