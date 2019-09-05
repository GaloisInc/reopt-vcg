def pmovsxbw1 : instruction :=
  definst "pmovsxbw" $ do
    pattern fun (v_2747 : reg (bv 128)) (v_2748 : reg (bv 128)) => do
      v_5460 <- getRegister v_2747;
      setRegister (lhs.of_reg v_2748) (concat (sext (extract v_5460 64 72) 16) (concat (sext (extract v_5460 72 80) 16) (concat (sext (extract v_5460 80 88) 16) (concat (sext (extract v_5460 88 96) 16) (concat (sext (extract v_5460 96 104) 16) (concat (sext (extract v_5460 104 112) 16) (concat (sext (extract v_5460 112 120) 16) (sext (extract v_5460 120 128) 16))))))));
      pure ()
    pat_end;
    pattern fun (v_2744 : Mem) (v_2743 : reg (bv 128)) => do
      v_12254 <- evaluateAddress v_2744;
      v_12255 <- load v_12254 8;
      setRegister (lhs.of_reg v_2743) (concat (sext (extract v_12255 0 8) 16) (concat (sext (extract v_12255 8 16) 16) (concat (sext (extract v_12255 16 24) 16) (concat (sext (extract v_12255 24 32) 16) (concat (sext (extract v_12255 32 40) 16) (concat (sext (extract v_12255 40 48) 16) (concat (sext (extract v_12255 48 56) 16) (sext (extract v_12255 56 64) 16))))))));
      pure ()
    pat_end
