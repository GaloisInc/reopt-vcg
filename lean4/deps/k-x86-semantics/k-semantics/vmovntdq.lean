def vmovntdq1 : instruction :=
  definst "vmovntdq" $ do
    pattern fun (v_2987 : reg (bv 256)) (v_2986 : Mem) => do
      v_9384 <- evaluateAddress v_2986;
      v_9385 <- getRegister v_2987;
      store v_9384 v_9385 32;
      pure ()
    pat_end;
    pattern fun (v_2983 : reg (bv 128)) (v_2982 : Mem) => do
      v_12463 <- evaluateAddress v_2982;
      v_12464 <- getRegister v_2983;
      store v_12463 v_12464 16;
      pure ()
    pat_end
