def movntpd1 : instruction :=
  definst "movntpd" $ do
    pattern fun (v_2613 : reg (bv 128)) (v_2612 : Mem) => do
      v_8468 <- evaluateAddress v_2612;
      v_8469 <- getRegister v_2613;
      store v_8468 v_8469 16;
      pure ()
    pat_end
