def vmovupd1 : instruction :=
  definst "vmovupd" $ do
    pattern fun (v_3020 : Mem) (v_3021 : reg (bv 128)) => do
      v_10406 <- evaluateAddress v_3020;
      v_10407 <- load v_10406 16;
      setRegister (lhs.of_reg v_3021) v_10407;
      pure ()
    pat_end;
    pattern fun (v_3029 : Mem) (v_3030 : reg (bv 256)) => do
      v_10409 <- evaluateAddress v_3029;
      v_10410 <- load v_10409 32;
      setRegister (lhs.of_reg v_3030) v_10410;
      pure ()
    pat_end;
    pattern fun (v_3013 : reg (bv 128)) (v_3012 : Mem) => do
      v_12779 <- evaluateAddress v_3012;
      v_12780 <- getRegister v_3013;
      store v_12779 v_12780 16;
      pure ()
    pat_end;
    pattern fun (v_3017 : reg (bv 256)) (v_3016 : Mem) => do
      v_12782 <- evaluateAddress v_3016;
      v_12783 <- getRegister v_3017;
      store v_12782 v_12783 32;
      pure ()
    pat_end
