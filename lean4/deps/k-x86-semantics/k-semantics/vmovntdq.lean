def vmovntdq1 : instruction :=
  definst "vmovntdq" $ do
    pattern fun (v_2898 : reg (bv 256)) (v_2897 : Mem) => do
      v_9467 <- evaluateAddress v_2897;
      v_9468 <- getRegister v_2898;
      store v_9467 v_9468 32;
      pure ()
    pat_end;
    pattern fun (v_2894 : reg (bv 128)) (v_2893 : Mem) => do
      v_12756 <- evaluateAddress v_2893;
      v_12757 <- getRegister v_2894;
      store v_12756 v_12757 16;
      pure ()
    pat_end
