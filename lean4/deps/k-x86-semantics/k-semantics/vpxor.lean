def vpxor1 : instruction :=
  definst "vpxor" $ do
    pattern fun (v_2841 : Mem) (v_2842 : reg (bv 128)) (v_2843 : reg (bv 128)) => do
      v_12594 <- getRegister v_2842;
      v_12595 <- evaluateAddress v_2841;
      v_12596 <- load v_12595 16;
      setRegister (lhs.of_reg v_2843) (bv_xor v_12594 v_12596);
      pure ()
    pat_end;
    pattern fun (v_2852 : Mem) (v_2853 : reg (bv 256)) (v_2854 : reg (bv 256)) => do
      v_12599 <- getRegister v_2853;
      v_12600 <- evaluateAddress v_2852;
      v_12601 <- load v_12600 32;
      setRegister (lhs.of_reg v_2854) (bv_xor v_12599 v_12601);
      pure ()
    pat_end
