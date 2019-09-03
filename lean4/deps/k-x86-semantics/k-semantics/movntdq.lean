def movntdq1 : instruction :=
  definst "movntdq" $ do
    pattern fun (v_2534 : reg (bv 128)) (v_2533 : Mem) => do
      v_8614 <- evaluateAddress v_2533;
      v_8615 <- getRegister v_2534;
      store v_8614 v_8615 16;
      pure ()
    pat_end
