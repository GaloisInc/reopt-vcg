def movntdq1 : instruction :=
  definst "movntdq" $ do
    pattern fun (v_2597 : reg (bv 128)) (v_2596 : Mem) => do
      v_8458 <- evaluateAddress v_2596;
      v_8459 <- getRegister v_2597;
      store v_8458 v_8459 16;
      pure ()
    pat_end
