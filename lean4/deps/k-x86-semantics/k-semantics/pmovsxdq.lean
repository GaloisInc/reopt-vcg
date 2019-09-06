def pmovsxdq1 : instruction :=
  definst "pmovsxdq" $ do
    pattern fun (v_2784 : reg (bv 128)) (v_2785 : reg (bv 128)) => do
      v_5516 <- getRegister v_2784;
      setRegister (lhs.of_reg v_2785) (concat (sext (extract v_5516 64 96) 64) (sext (extract v_5516 96 128) 64));
      pure ()
    pat_end;
    pattern fun (v_2780 : Mem) (v_2781 : reg (bv 128)) => do
      v_12256 <- evaluateAddress v_2780;
      v_12257 <- load v_12256 8;
      setRegister (lhs.of_reg v_2781) (concat (sext (extract v_12257 0 32) 64) (sext (extract v_12257 32 64) 64));
      pure ()
    pat_end
