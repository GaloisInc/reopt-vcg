def vmovntps1 : instruction :=
  definst "vmovntps" $ do
    pattern fun (v_2982 : reg (bv 128)) (v_2981 : Mem) => do
      v_12445 <- evaluateAddress v_2981;
      v_12446 <- getRegister v_2982;
      store v_12445 v_12446 16;
      pure ()
    pat_end;
    pattern fun (v_2986 : reg (bv 256)) (v_2985 : Mem) => do
      v_12448 <- evaluateAddress v_2985;
      v_12449 <- getRegister v_2986;
      store v_12448 v_12449 32;
      pure ()
    pat_end
