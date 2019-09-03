def vpmovsxbd1 : instruction :=
  definst "vpmovsxbd" $ do
    pattern fun (v_2603 : reg (bv 128)) (v_2604 : reg (bv 128)) => do
      v_5417 <- getRegister v_2603;
      setRegister (lhs.of_reg v_2604) (concat (leanSignExtend (extract v_5417 96 104) 32) (concat (leanSignExtend (extract v_5417 104 112) 32) (concat (leanSignExtend (extract v_5417 112 120) 32) (leanSignExtend (extract v_5417 120 128) 32))));
      pure ()
    pat_end;
    pattern fun (v_2612 : reg (bv 128)) (v_2614 : reg (bv 256)) => do
      v_5434 <- getRegister v_2612;
      setRegister (lhs.of_reg v_2614) (concat (leanSignExtend (extract v_5434 64 72) 32) (concat (leanSignExtend (extract v_5434 72 80) 32) (concat (leanSignExtend (extract v_5434 80 88) 32) (concat (leanSignExtend (extract v_5434 88 96) 32) (concat (leanSignExtend (extract v_5434 96 104) 32) (concat (leanSignExtend (extract v_5434 104 112) 32) (concat (leanSignExtend (extract v_5434 112 120) 32) (leanSignExtend (extract v_5434 120 128) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2598 : Mem) (v_2599 : reg (bv 128)) => do
      v_12104 <- evaluateAddress v_2598;
      v_12105 <- load v_12104 4;
      setRegister (lhs.of_reg v_2599) (concat (leanSignExtend (extract v_12105 0 8) 32) (concat (leanSignExtend (extract v_12105 8 16) 32) (concat (leanSignExtend (extract v_12105 16 24) 32) (leanSignExtend (extract v_12105 24 32) 32))));
      pure ()
    pat_end;
    pattern fun (v_2607 : Mem) (v_2609 : reg (bv 256)) => do
      v_12118 <- evaluateAddress v_2607;
      v_12119 <- load v_12118 8;
      setRegister (lhs.of_reg v_2609) (concat (leanSignExtend (extract v_12119 0 8) 32) (concat (leanSignExtend (extract v_12119 8 16) 32) (concat (leanSignExtend (extract v_12119 16 24) 32) (concat (leanSignExtend (extract v_12119 24 32) 32) (concat (leanSignExtend (extract v_12119 32 40) 32) (concat (leanSignExtend (extract v_12119 40 48) 32) (concat (leanSignExtend (extract v_12119 48 56) 32) (leanSignExtend (extract v_12119 56 64) 32))))))));
      pure ()
    pat_end
