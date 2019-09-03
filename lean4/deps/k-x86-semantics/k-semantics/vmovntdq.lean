def vmovntdq1 : instruction :=
  definst "vmovntdq" $ do
    pattern fun (v_2911 : reg (bv 256)) (v_2910 : Mem) => do
      v_9912 <- evaluateAddress v_2910;
      v_9913 <- getRegister v_2911;
      store v_9912 v_9913 32;
      pure ()
    pat_end;
    pattern fun (v_2907 : reg (bv 128)) (v_2906 : Mem) => do
      v_13633 <- evaluateAddress v_2906;
      v_13634 <- getRegister v_2907;
      store v_13633 v_13634 16;
      pure ()
    pat_end
