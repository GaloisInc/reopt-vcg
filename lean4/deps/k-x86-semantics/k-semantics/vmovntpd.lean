def vmovntpd1 : instruction :=
  definst "vmovntpd" $ do
    pattern fun (v_2999 : reg (bv 128)) (v_2998 : Mem) => do
      v_12466 <- evaluateAddress v_2998;
      v_12467 <- getRegister v_2999;
      store v_12466 v_12467 16;
      pure ()
    pat_end;
    pattern fun (v_3003 : reg (bv 256)) (v_3002 : Mem) => do
      v_12469 <- evaluateAddress v_3002;
      v_12470 <- getRegister v_3003;
      store v_12469 v_12470 32;
      pure ()
    pat_end
