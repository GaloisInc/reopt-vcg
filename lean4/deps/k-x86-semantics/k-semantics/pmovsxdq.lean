def pmovsxdq1 : instruction :=
  definst "pmovsxdq" $ do
    pattern fun (v_2756 : reg (bv 128)) (v_2757 : reg (bv 128)) => do
      v_5489 <- getRegister v_2756;
      setRegister (lhs.of_reg v_2757) (concat (sext (extract v_5489 64 96) 64) (sext (extract v_5489 96 128) 64));
      pure ()
    pat_end;
    pattern fun (v_2753 : Mem) (v_2752 : reg (bv 128)) => do
      v_12280 <- evaluateAddress v_2753;
      v_12281 <- load v_12280 8;
      setRegister (lhs.of_reg v_2752) (concat (sext (extract v_12281 0 32) 64) (sext (extract v_12281 32 64) 64));
      pure ()
    pat_end
