def vpmovsxbw1 : instruction :=
  definst "vpmovsxbw" $ do
    pattern fun (v_2719 : reg (bv 128)) (v_2720 : reg (bv 128)) => do
      v_5569 <- getRegister v_2719;
      setRegister (lhs.of_reg v_2720) (concat (sext (extract v_5569 64 72) 16) (concat (sext (extract v_5569 72 80) 16) (concat (sext (extract v_5569 80 88) 16) (concat (sext (extract v_5569 88 96) 16) (concat (sext (extract v_5569 96 104) 16) (concat (sext (extract v_5569 104 112) 16) (concat (sext (extract v_5569 112 120) 16) (sext (extract v_5569 120 128) 16))))))));
      pure ()
    pat_end;
    pattern fun (v_2729 : reg (bv 128)) (v_2728 : reg (bv 256)) => do
      v_5598 <- getRegister v_2729;
      setRegister (lhs.of_reg v_2728) (concat (sext (extract v_5598 0 8) 16) (concat (sext (extract v_5598 8 16) 16) (concat (sext (extract v_5598 16 24) 16) (concat (sext (extract v_5598 24 32) 16) (concat (sext (extract v_5598 32 40) 16) (concat (sext (extract v_5598 40 48) 16) (concat (sext (extract v_5598 48 56) 16) (concat (sext (extract v_5598 56 64) 16) (concat (sext (extract v_5598 64 72) 16) (concat (sext (extract v_5598 72 80) 16) (concat (sext (extract v_5598 80 88) 16) (concat (sext (extract v_5598 88 96) 16) (concat (sext (extract v_5598 96 104) 16) (concat (sext (extract v_5598 104 112) 16) (concat (sext (extract v_5598 112 120) 16) (sext (extract v_5598 120 128) 16))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2714 : Mem) (v_2715 : reg (bv 128)) => do
      v_11988 <- evaluateAddress v_2714;
      v_11989 <- load v_11988 8;
      setRegister (lhs.of_reg v_2715) (concat (sext (extract v_11989 0 8) 16) (concat (sext (extract v_11989 8 16) 16) (concat (sext (extract v_11989 16 24) 16) (concat (sext (extract v_11989 24 32) 16) (concat (sext (extract v_11989 32 40) 16) (concat (sext (extract v_11989 40 48) 16) (concat (sext (extract v_11989 48 56) 16) (sext (extract v_11989 56 64) 16))))))));
      pure ()
    pat_end;
    pattern fun (v_2723 : Mem) (v_2724 : reg (bv 256)) => do
      v_12014 <- evaluateAddress v_2723;
      v_12015 <- load v_12014 16;
      setRegister (lhs.of_reg v_2724) (concat (sext (extract v_12015 0 8) 16) (concat (sext (extract v_12015 8 16) 16) (concat (sext (extract v_12015 16 24) 16) (concat (sext (extract v_12015 24 32) 16) (concat (sext (extract v_12015 32 40) 16) (concat (sext (extract v_12015 40 48) 16) (concat (sext (extract v_12015 48 56) 16) (concat (sext (extract v_12015 56 64) 16) (concat (sext (extract v_12015 64 72) 16) (concat (sext (extract v_12015 72 80) 16) (concat (sext (extract v_12015 80 88) 16) (concat (sext (extract v_12015 88 96) 16) (concat (sext (extract v_12015 96 104) 16) (concat (sext (extract v_12015 104 112) 16) (concat (sext (extract v_12015 112 120) 16) (sext (extract v_12015 120 128) 16))))))))))))))));
      pure ()
    pat_end
