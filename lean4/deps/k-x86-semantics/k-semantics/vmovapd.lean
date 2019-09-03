def vmovapd1 : instruction :=
  definst "vmovapd" $ do
    pattern fun (v_2673 : Mem) (v_2674 : reg (bv 128)) => do
      v_10260 <- evaluateAddress v_2673;
      v_10261 <- load v_10260 16;
      setRegister (lhs.of_reg v_2674) v_10261;
      pure ()
    pat_end;
    pattern fun (v_2682 : Mem) (v_2683 : reg (bv 256)) => do
      v_10263 <- evaluateAddress v_2682;
      v_10264 <- load v_10263 32;
      setRegister (lhs.of_reg v_2683) v_10264;
      pure ()
    pat_end;
    pattern fun (v_2666 : reg (bv 128)) (v_2665 : Mem) => do
      v_12722 <- evaluateAddress v_2665;
      v_12723 <- getRegister v_2666;
      store v_12722 v_12723 16;
      pure ()
    pat_end;
    pattern fun (v_2670 : reg (bv 256)) (v_2669 : Mem) => do
      v_12725 <- evaluateAddress v_2669;
      v_12726 <- getRegister v_2670;
      store v_12725 v_12726 32;
      pure ()
    pat_end
