def vmovntpd1 : instruction :=
  definst "vmovntpd" $ do
    pattern fun (v_2923 : reg (bv 128)) (v_2922 : Mem) => do
      v_13636 <- evaluateAddress v_2922;
      v_13637 <- getRegister v_2923;
      store v_13636 v_13637 16;
      pure ()
    pat_end;
    pattern fun (v_2927 : reg (bv 256)) (v_2926 : Mem) => do
      v_13639 <- evaluateAddress v_2926;
      v_13640 <- getRegister v_2927;
      store v_13639 v_13640 32;
      pure ()
    pat_end
