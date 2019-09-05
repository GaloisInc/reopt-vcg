def vmovapd1 : instruction :=
  definst "vmovapd" $ do
    pattern fun (v_2737 : Mem) (v_2738 : reg (bv 128)) => do
      v_10126 <- evaluateAddress v_2737;
      v_10127 <- load v_10126 16;
      setRegister (lhs.of_reg v_2738) v_10127;
      pure ()
    pat_end;
    pattern fun (v_2746 : Mem) (v_2747 : reg (bv 256)) => do
      v_10129 <- evaluateAddress v_2746;
      v_10130 <- load v_10129 32;
      setRegister (lhs.of_reg v_2747) v_10130;
      pure ()
    pat_end;
    pattern fun (v_2730 : reg (bv 128)) (v_2729 : Mem) => do
      v_12402 <- evaluateAddress v_2729;
      v_12403 <- getRegister v_2730;
      store v_12402 v_12403 16;
      pure ()
    pat_end;
    pattern fun (v_2734 : reg (bv 256)) (v_2733 : Mem) => do
      v_12405 <- evaluateAddress v_2733;
      v_12406 <- getRegister v_2734;
      store v_12405 v_12406 32;
      pure ()
    pat_end
