def vpxor1 : instruction :=
  definst "vpxor" $ do
    pattern fun (v_2750 : Mem) (v_2751 : reg (bv 128)) (v_2752 : reg (bv 128)) => do
      v_12894 <- getRegister v_2751;
      v_12895 <- evaluateAddress v_2750;
      v_12896 <- load v_12895 16;
      setRegister (lhs.of_reg v_2752) (bv_xor v_12894 v_12896);
      pure ()
    pat_end;
    pattern fun (v_2761 : Mem) (v_2762 : reg (bv 256)) (v_2763 : reg (bv 256)) => do
      v_12899 <- getRegister v_2762;
      v_12900 <- evaluateAddress v_2761;
      v_12901 <- load v_12900 32;
      setRegister (lhs.of_reg v_2763) (bv_xor v_12899 v_12901);
      pure ()
    pat_end
