def vmovntdq1 : instruction :=
  definst "vmovntdq" $ do
    pattern fun (v_2962 : reg (bv 256)) (v_2961 : Mem) => do
      v_9357 <- evaluateAddress v_2961;
      v_9358 <- getRegister v_2962;
      store v_9357 v_9358 32;
      pure ()
    pat_end;
    pattern fun (v_2958 : reg (bv 128)) (v_2957 : Mem) => do
      v_12436 <- evaluateAddress v_2957;
      v_12437 <- getRegister v_2958;
      store v_12436 v_12437 16;
      pure ()
    pat_end
