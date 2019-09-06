def movntdq1 : instruction :=
  definst "movntdq" $ do
    pattern fun (v_2623 : reg (bv 128)) (v_2622 : Mem) => do
      v_8485 <- evaluateAddress v_2622;
      v_8486 <- getRegister v_2623;
      store v_8485 v_8486 16;
      pure ()
    pat_end
