def pmovsxbw1 : instruction :=
  definst "pmovsxbw" $ do
    pattern fun (v_2698 : reg (bv 128)) (v_2699 : reg (bv 128)) => do
      v_5429 <- getRegister v_2698;
      setRegister (lhs.of_reg v_2699) (concat (leanSignExtend (extract v_5429 64 72) 16) (concat (leanSignExtend (extract v_5429 72 80) 16) (concat (leanSignExtend (extract v_5429 80 88) 16) (concat (leanSignExtend (extract v_5429 88 96) 16) (concat (leanSignExtend (extract v_5429 96 104) 16) (concat (leanSignExtend (extract v_5429 104 112) 16) (concat (leanSignExtend (extract v_5429 112 120) 16) (leanSignExtend (extract v_5429 120 128) 16))))))));
      pure ()
    pat_end;
    pattern fun (v_2694 : Mem) (v_2695 : reg (bv 128)) => do
      v_12396 <- evaluateAddress v_2694;
      v_12397 <- load v_12396 8;
      setRegister (lhs.of_reg v_2695) (concat (leanSignExtend (extract v_12397 0 8) 16) (concat (leanSignExtend (extract v_12397 8 16) 16) (concat (leanSignExtend (extract v_12397 16 24) 16) (concat (leanSignExtend (extract v_12397 24 32) 16) (concat (leanSignExtend (extract v_12397 32 40) 16) (concat (leanSignExtend (extract v_12397 40 48) 16) (concat (leanSignExtend (extract v_12397 48 56) 16) (leanSignExtend (extract v_12397 56 64) 16))))))));
      pure ()
    pat_end
