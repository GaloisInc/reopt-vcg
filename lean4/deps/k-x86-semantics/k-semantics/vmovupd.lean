def vmovupd1 : instruction :=
  definst "vmovupd" $ do
    pattern fun (v_3033 : Mem) (v_3034 : reg (bv 128)) => do
      v_11211 <- evaluateAddress v_3033;
      v_11212 <- load v_11211 16;
      setRegister (lhs.of_reg v_3034) v_11212;
      pure ()
    pat_end;
    pattern fun (v_3042 : Mem) (v_3043 : reg (bv 256)) => do
      v_11214 <- evaluateAddress v_3042;
      v_11215 <- load v_11214 32;
      setRegister (lhs.of_reg v_3043) v_11215;
      pure ()
    pat_end;
    pattern fun (v_3026 : reg (bv 128)) (v_3025 : Mem) => do
      v_13656 <- evaluateAddress v_3025;
      v_13657 <- getRegister v_3026;
      store v_13656 v_13657 16;
      pure ()
    pat_end;
    pattern fun (v_3030 : reg (bv 256)) (v_3029 : Mem) => do
      v_13659 <- evaluateAddress v_3029;
      v_13660 <- getRegister v_3030;
      store v_13659 v_13660 32;
      pure ()
    pat_end
