def vmovdqu1 : instruction :=
  definst "vmovdqu" $ do
    pattern fun (v_2800 : Mem) (v_2801 : reg (bv 128)) => do
      v_11106 <- evaluateAddress v_2800;
      v_11107 <- load v_11106 16;
      setRegister (lhs.of_reg v_2801) v_11107;
      pure ()
    pat_end;
    pattern fun (v_2809 : Mem) (v_2810 : reg (bv 256)) => do
      v_11109 <- evaluateAddress v_2809;
      v_11110 <- load v_11109 32;
      setRegister (lhs.of_reg v_2810) v_11110;
      pure ()
    pat_end;
    pattern fun (v_2793 : reg (bv 128)) (v_2792 : Mem) => do
      v_13611 <- evaluateAddress v_2792;
      v_13612 <- getRegister v_2793;
      store v_13611 v_13612 16;
      pure ()
    pat_end;
    pattern fun (v_2797 : reg (bv 256)) (v_2796 : Mem) => do
      v_13614 <- evaluateAddress v_2796;
      v_13615 <- getRegister v_2797;
      store v_13614 v_13615 32;
      pure ()
    pat_end
