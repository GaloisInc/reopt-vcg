def movntdq1 : instruction :=
  definst "movntdq" $ do
    pattern fun (v_2547 : reg (bv 128)) (v_2546 : Mem) => do
      v_8594 <- evaluateAddress v_2546;
      v_8595 <- getRegister v_2547;
      store v_8594 v_8595 16;
      pure ()
    pat_end
