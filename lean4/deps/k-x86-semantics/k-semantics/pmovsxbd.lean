def pmovsxbd1 : instruction :=
  definst "pmovsxbd" $ do
    pattern fun (v_2680 : reg (bv 128)) (v_2681 : reg (bv 128)) => do
      v_5401 <- getRegister v_2680;
      setRegister (lhs.of_reg v_2681) (concat (leanSignExtend (extract v_5401 96 104) 32) (concat (leanSignExtend (extract v_5401 104 112) 32) (concat (leanSignExtend (extract v_5401 112 120) 32) (leanSignExtend (extract v_5401 120 128) 32))));
      pure ()
    pat_end;
    pattern fun (v_2676 : Mem) (v_2677 : reg (bv 128)) => do
      v_12374 <- evaluateAddress v_2676;
      v_12375 <- load v_12374 4;
      setRegister (lhs.of_reg v_2677) (concat (leanSignExtend (extract v_12375 0 8) 32) (concat (leanSignExtend (extract v_12375 8 16) 32) (concat (leanSignExtend (extract v_12375 16 24) 32) (leanSignExtend (extract v_12375 24 32) 32))));
      pure ()
    pat_end
