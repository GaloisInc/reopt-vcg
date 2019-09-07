def movntdq1 : instruction :=
  definst "movntdq" $ do
    pattern fun (xmm_0 : reg (bv 128)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister xmm_0;
      store v_2 v_3 16;
      pure ()
    pat_end
