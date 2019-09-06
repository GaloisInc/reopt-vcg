def vmovapd1 : instruction :=
  definst "vmovapd" $ do
    pattern fun (v_2762 : Mem) (v_2763 : reg (bv 128)) => do
      v_10153 <- evaluateAddress v_2762;
      v_10154 <- load v_10153 16;
      setRegister (lhs.of_reg v_2763) v_10154;
      pure ()
    pat_end;
    pattern fun (v_2771 : Mem) (v_2772 : reg (bv 256)) => do
      v_10156 <- evaluateAddress v_2771;
      v_10157 <- load v_10156 32;
      setRegister (lhs.of_reg v_2772) v_10157;
      pure ()
    pat_end;
    pattern fun (v_2755 : reg (bv 128)) (v_2754 : Mem) => do
      v_12429 <- evaluateAddress v_2754;
      v_12430 <- getRegister v_2755;
      store v_12429 v_12430 16;
      pure ()
    pat_end;
    pattern fun (v_2759 : reg (bv 256)) (v_2758 : Mem) => do
      v_12432 <- evaluateAddress v_2758;
      v_12433 <- getRegister v_2759;
      store v_12432 v_12433 32;
      pure ()
    pat_end
