def xorpd1 : instruction :=
  definst "xorpd" $ do
    pattern fun (v_2795 : reg (bv 128)) (v_2796 : reg (bv 128)) => do
      v_5038 <- getRegister v_2796;
      v_5039 <- getRegister v_2795;
      setRegister (lhs.of_reg v_2796) (bv_xor v_5038 v_5039);
      pure ()
    pat_end;
    pattern fun (v_2791 : Mem) (v_2792 : reg (bv 128)) => do
      v_7246 <- getRegister v_2792;
      v_7247 <- evaluateAddress v_2791;
      v_7248 <- load v_7247 16;
      setRegister (lhs.of_reg v_2792) (bv_xor v_7246 v_7248);
      pure ()
    pat_end
