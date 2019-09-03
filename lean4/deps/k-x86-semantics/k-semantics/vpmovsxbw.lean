def vpmovsxbw1 : instruction :=
  definst "vpmovsxbw" $ do
    pattern fun (v_2639 : reg (bv 128)) (v_2640 : reg (bv 128)) => do
      v_5491 <- getRegister v_2639;
      setRegister (lhs.of_reg v_2640) (concat (leanSignExtend (extract v_5491 64 72) 16) (concat (leanSignExtend (extract v_5491 72 80) 16) (concat (leanSignExtend (extract v_5491 80 88) 16) (concat (leanSignExtend (extract v_5491 88 96) 16) (concat (leanSignExtend (extract v_5491 96 104) 16) (concat (leanSignExtend (extract v_5491 104 112) 16) (concat (leanSignExtend (extract v_5491 112 120) 16) (leanSignExtend (extract v_5491 120 128) 16))))))));
      pure ()
    pat_end;
    pattern fun (v_2648 : reg (bv 128)) (v_2650 : reg (bv 256)) => do
      v_5520 <- getRegister v_2648;
      setRegister (lhs.of_reg v_2650) (concat (leanSignExtend (extract v_5520 0 8) 16) (concat (leanSignExtend (extract v_5520 8 16) 16) (concat (leanSignExtend (extract v_5520 16 24) 16) (concat (leanSignExtend (extract v_5520 24 32) 16) (concat (leanSignExtend (extract v_5520 32 40) 16) (concat (leanSignExtend (extract v_5520 40 48) 16) (concat (leanSignExtend (extract v_5520 48 56) 16) (concat (leanSignExtend (extract v_5520 56 64) 16) (concat (leanSignExtend (extract v_5520 64 72) 16) (concat (leanSignExtend (extract v_5520 72 80) 16) (concat (leanSignExtend (extract v_5520 80 88) 16) (concat (leanSignExtend (extract v_5520 88 96) 16) (concat (leanSignExtend (extract v_5520 96 104) 16) (concat (leanSignExtend (extract v_5520 104 112) 16) (concat (leanSignExtend (extract v_5520 112 120) 16) (leanSignExtend (extract v_5520 120 128) 16))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2634 : Mem) (v_2635 : reg (bv 128)) => do
      v_12166 <- evaluateAddress v_2634;
      v_12167 <- load v_12166 8;
      setRegister (lhs.of_reg v_2635) (concat (leanSignExtend (extract v_12167 0 8) 16) (concat (leanSignExtend (extract v_12167 8 16) 16) (concat (leanSignExtend (extract v_12167 16 24) 16) (concat (leanSignExtend (extract v_12167 24 32) 16) (concat (leanSignExtend (extract v_12167 32 40) 16) (concat (leanSignExtend (extract v_12167 40 48) 16) (concat (leanSignExtend (extract v_12167 48 56) 16) (leanSignExtend (extract v_12167 56 64) 16))))))));
      pure ()
    pat_end;
    pattern fun (v_2643 : Mem) (v_2645 : reg (bv 256)) => do
      v_12192 <- evaluateAddress v_2643;
      v_12193 <- load v_12192 16;
      setRegister (lhs.of_reg v_2645) (concat (leanSignExtend (extract v_12193 0 8) 16) (concat (leanSignExtend (extract v_12193 8 16) 16) (concat (leanSignExtend (extract v_12193 16 24) 16) (concat (leanSignExtend (extract v_12193 24 32) 16) (concat (leanSignExtend (extract v_12193 32 40) 16) (concat (leanSignExtend (extract v_12193 40 48) 16) (concat (leanSignExtend (extract v_12193 48 56) 16) (concat (leanSignExtend (extract v_12193 56 64) 16) (concat (leanSignExtend (extract v_12193 64 72) 16) (concat (leanSignExtend (extract v_12193 72 80) 16) (concat (leanSignExtend (extract v_12193 80 88) 16) (concat (leanSignExtend (extract v_12193 88 96) 16) (concat (leanSignExtend (extract v_12193 96 104) 16) (concat (leanSignExtend (extract v_12193 104 112) 16) (concat (leanSignExtend (extract v_12193 112 120) 16) (leanSignExtend (extract v_12193 120 128) 16))))))))))))))));
      pure ()
    pat_end
