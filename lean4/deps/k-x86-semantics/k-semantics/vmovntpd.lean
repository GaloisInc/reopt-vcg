def vmovntpd1 : instruction :=
  definst "vmovntpd" $ do
    pattern fun (v_2974 : reg (bv 128)) (v_2973 : Mem) => do
      v_12439 <- evaluateAddress v_2973;
      v_12440 <- getRegister v_2974;
      store v_12439 v_12440 16;
      pure ()
    pat_end;
    pattern fun (v_2978 : reg (bv 256)) (v_2977 : Mem) => do
      v_12442 <- evaluateAddress v_2977;
      v_12443 <- getRegister v_2978;
      store v_12442 v_12443 32;
      pure ()
    pat_end
