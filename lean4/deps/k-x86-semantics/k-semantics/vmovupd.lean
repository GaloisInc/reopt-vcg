def vmovupd1 : instruction :=
  definst "vmovupd" $ do
    pattern fun (v_3109 : Mem) (v_3110 : reg (bv 128)) => do
      v_10299 <- evaluateAddress v_3109;
      v_10300 <- load v_10299 16;
      setRegister (lhs.of_reg v_3110) v_10300;
      pure ()
    pat_end;
    pattern fun (v_3118 : Mem) (v_3119 : reg (bv 256)) => do
      v_10302 <- evaluateAddress v_3118;
      v_10303 <- load v_10302 32;
      setRegister (lhs.of_reg v_3119) v_10303;
      pure ()
    pat_end;
    pattern fun (v_3102 : reg (bv 128)) (v_3101 : Mem) => do
      v_12486 <- evaluateAddress v_3101;
      v_12487 <- getRegister v_3102;
      store v_12486 v_12487 16;
      pure ()
    pat_end;
    pattern fun (v_3106 : reg (bv 256)) (v_3105 : Mem) => do
      v_12489 <- evaluateAddress v_3105;
      v_12490 <- getRegister v_3106;
      store v_12489 v_12490 32;
      pure ()
    pat_end
