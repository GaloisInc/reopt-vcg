def movapd1 : instruction :=
  definst "movapd" $ do
    pattern fun (v_3127 : reg (bv 128)) (v_3128 : reg (bv 128)) => do
      v_5885 <- getRegister v_3127;
      setRegister (lhs.of_reg v_3128) v_5885;
      pure ()
    pat_end;
    pattern fun (v_3120 : reg (bv 128)) (v_3119 : Mem) => do
      v_7661 <- evaluateAddress v_3119;
      v_7662 <- getRegister v_3120;
      store v_7661 v_7662 16;
      pure ()
    pat_end;
    pattern fun (v_3123 : Mem) (v_3124 : reg (bv 128)) => do
      v_9306 <- evaluateAddress v_3123;
      v_9307 <- load v_9306 16;
      setRegister (lhs.of_reg v_3124) v_9307;
      pure ()
    pat_end
