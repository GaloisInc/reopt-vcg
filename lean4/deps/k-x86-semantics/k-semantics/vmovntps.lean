def vmovntps1 : instruction :=
  definst "vmovntps" $ do
    pattern fun (v_2931 : reg (bv 128)) (v_2930 : Mem) => do
      v_13642 <- evaluateAddress v_2930;
      v_13643 <- getRegister v_2931;
      store v_13642 v_13643 16;
      pure ()
    pat_end;
    pattern fun (v_2935 : reg (bv 256)) (v_2934 : Mem) => do
      v_13645 <- evaluateAddress v_2934;
      v_13646 <- getRegister v_2935;
      store v_13645 v_13646 32;
      pure ()
    pat_end
