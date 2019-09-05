def vpmovsxdq1 : instruction :=
  definst "vpmovsxdq" $ do
    pattern fun (v_2710 : reg (bv 128)) (v_2711 : reg (bv 128)) => do
      v_5624 <- getRegister v_2710;
      setRegister (lhs.of_reg v_2711) (concat (sext (extract v_5624 64 96) 64) (sext (extract v_5624 96 128) 64));
      pure ()
    pat_end;
    pattern fun (v_2720 : reg (bv 128)) (v_2719 : reg (bv 256)) => do
      v_5635 <- getRegister v_2720;
      setRegister (lhs.of_reg v_2719) (concat (sext (extract v_5635 0 32) 64) (concat (sext (extract v_5635 32 64) 64) (concat (sext (extract v_5635 64 96) 64) (sext (extract v_5635 96 128) 64))));
      pure ()
    pat_end;
    pattern fun (v_2705 : Mem) (v_2706 : reg (bv 128)) => do
      v_12037 <- evaluateAddress v_2705;
      v_12038 <- load v_12037 8;
      setRegister (lhs.of_reg v_2706) (concat (sext (extract v_12038 0 32) 64) (sext (extract v_12038 32 64) 64));
      pure ()
    pat_end;
    pattern fun (v_2714 : Mem) (v_2715 : reg (bv 256)) => do
      v_12045 <- evaluateAddress v_2714;
      v_12046 <- load v_12045 16;
      setRegister (lhs.of_reg v_2715) (concat (sext (extract v_12046 0 32) 64) (concat (sext (extract v_12046 32 64) 64) (concat (sext (extract v_12046 64 96) 64) (sext (extract v_12046 96 128) 64))));
      pure ()
    pat_end
