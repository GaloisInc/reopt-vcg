def pmullw1 : instruction :=
  definst "pmullw" $ do
    pattern fun (v_2833 : reg (bv 128)) (v_2834 : reg (bv 128)) => do
      v_5847 <- getRegister v_2834;
      v_5850 <- getRegister v_2833;
      setRegister (lhs.of_reg v_2834) (concat (extract (mul (leanSignExtend (extract v_5847 0 16) 32) (leanSignExtend (extract v_5850 0 16) 32)) 16 32) (concat (extract (mul (leanSignExtend (extract v_5847 16 32) 32) (leanSignExtend (extract v_5850 16 32) 32)) 16 32) (concat (extract (mul (leanSignExtend (extract v_5847 32 48) 32) (leanSignExtend (extract v_5850 32 48) 32)) 16 32) (concat (extract (mul (leanSignExtend (extract v_5847 48 64) 32) (leanSignExtend (extract v_5850 48 64) 32)) 16 32) (concat (extract (mul (leanSignExtend (extract v_5847 64 80) 32) (leanSignExtend (extract v_5850 64 80) 32)) 16 32) (concat (extract (mul (leanSignExtend (extract v_5847 80 96) 32) (leanSignExtend (extract v_5850 80 96) 32)) 16 32) (concat (extract (mul (leanSignExtend (extract v_5847 96 112) 32) (leanSignExtend (extract v_5850 96 112) 32)) 16 32) (extract (mul (leanSignExtend (extract v_5847 112 128) 32) (leanSignExtend (extract v_5850 112 128) 32)) 16 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2829 : Mem) (v_2830 : reg (bv 128)) => do
      v_12769 <- getRegister v_2830;
      v_12772 <- evaluateAddress v_2829;
      v_12773 <- load v_12772 16;
      setRegister (lhs.of_reg v_2830) (concat (extract (mul (leanSignExtend (extract v_12769 0 16) 32) (leanSignExtend (extract v_12773 0 16) 32)) 16 32) (concat (extract (mul (leanSignExtend (extract v_12769 16 32) 32) (leanSignExtend (extract v_12773 16 32) 32)) 16 32) (concat (extract (mul (leanSignExtend (extract v_12769 32 48) 32) (leanSignExtend (extract v_12773 32 48) 32)) 16 32) (concat (extract (mul (leanSignExtend (extract v_12769 48 64) 32) (leanSignExtend (extract v_12773 48 64) 32)) 16 32) (concat (extract (mul (leanSignExtend (extract v_12769 64 80) 32) (leanSignExtend (extract v_12773 64 80) 32)) 16 32) (concat (extract (mul (leanSignExtend (extract v_12769 80 96) 32) (leanSignExtend (extract v_12773 80 96) 32)) 16 32) (concat (extract (mul (leanSignExtend (extract v_12769 96 112) 32) (leanSignExtend (extract v_12773 96 112) 32)) 16 32) (extract (mul (leanSignExtend (extract v_12769 112 128) 32) (leanSignExtend (extract v_12773 112 128) 32)) 16 32))))))));
      pure ()
    pat_end
