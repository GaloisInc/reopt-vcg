def vpmulld1 : instruction :=
  definst "vpmulld" $ do
    pattern fun (v_2908 : reg (bv 128)) (v_2909 : reg (bv 128)) (v_2910 : reg (bv 128)) => do
      v_6578 <- getRegister v_2909;
      v_6581 <- getRegister v_2908;
      setRegister (lhs.of_reg v_2910) (concat (extract (mul (leanSignExtend (extract v_6578 0 32) 64) (leanSignExtend (extract v_6581 0 32) 64)) 32 64) (concat (extract (mul (leanSignExtend (extract v_6578 32 64) 64) (leanSignExtend (extract v_6581 32 64) 64)) 32 64) (concat (extract (mul (leanSignExtend (extract v_6578 64 96) 64) (leanSignExtend (extract v_6581 64 96) 64)) 32 64) (extract (mul (leanSignExtend (extract v_6578 96 128) 64) (leanSignExtend (extract v_6581 96 128) 64)) 32 64))));
      pure ()
    pat_end;
    pattern fun (v_2920 : reg (bv 256)) (v_2921 : reg (bv 256)) (v_2922 : reg (bv 256)) => do
      v_6613 <- getRegister v_2921;
      v_6616 <- getRegister v_2920;
      setRegister (lhs.of_reg v_2922) (concat (extract (mul (leanSignExtend (extract v_6613 0 32) 64) (leanSignExtend (extract v_6616 0 32) 64)) 32 64) (concat (extract (mul (leanSignExtend (extract v_6613 32 64) 64) (leanSignExtend (extract v_6616 32 64) 64)) 32 64) (concat (extract (mul (leanSignExtend (extract v_6613 64 96) 64) (leanSignExtend (extract v_6616 64 96) 64)) 32 64) (concat (extract (mul (leanSignExtend (extract v_6613 96 128) 64) (leanSignExtend (extract v_6616 96 128) 64)) 32 64) (concat (extract (mul (leanSignExtend (extract v_6613 128 160) 64) (leanSignExtend (extract v_6616 128 160) 64)) 32 64) (concat (extract (mul (leanSignExtend (extract v_6613 160 192) 64) (leanSignExtend (extract v_6616 160 192) 64)) 32 64) (concat (extract (mul (leanSignExtend (extract v_6613 192 224) 64) (leanSignExtend (extract v_6616 192 224) 64)) 32 64) (extract (mul (leanSignExtend (extract v_6613 224 256) 64) (leanSignExtend (extract v_6616 224 256) 64)) 32 64))))))));
      pure ()
    pat_end;
    pattern fun (v_2902 : Mem) (v_2903 : reg (bv 128)) (v_2904 : reg (bv 128)) => do
      v_13160 <- getRegister v_2903;
      v_13163 <- evaluateAddress v_2902;
      v_13164 <- load v_13163 16;
      setRegister (lhs.of_reg v_2904) (concat (extract (mul (leanSignExtend (extract v_13160 0 32) 64) (leanSignExtend (extract v_13164 0 32) 64)) 32 64) (concat (extract (mul (leanSignExtend (extract v_13160 32 64) 64) (leanSignExtend (extract v_13164 32 64) 64)) 32 64) (concat (extract (mul (leanSignExtend (extract v_13160 64 96) 64) (leanSignExtend (extract v_13164 64 96) 64)) 32 64) (extract (mul (leanSignExtend (extract v_13160 96 128) 64) (leanSignExtend (extract v_13164 96 128) 64)) 32 64))));
      pure ()
    pat_end;
    pattern fun (v_2913 : Mem) (v_2915 : reg (bv 256)) (v_2916 : reg (bv 256)) => do
      v_13191 <- getRegister v_2915;
      v_13194 <- evaluateAddress v_2913;
      v_13195 <- load v_13194 32;
      setRegister (lhs.of_reg v_2916) (concat (extract (mul (leanSignExtend (extract v_13191 0 32) 64) (leanSignExtend (extract v_13195 0 32) 64)) 32 64) (concat (extract (mul (leanSignExtend (extract v_13191 32 64) 64) (leanSignExtend (extract v_13195 32 64) 64)) 32 64) (concat (extract (mul (leanSignExtend (extract v_13191 64 96) 64) (leanSignExtend (extract v_13195 64 96) 64)) 32 64) (concat (extract (mul (leanSignExtend (extract v_13191 96 128) 64) (leanSignExtend (extract v_13195 96 128) 64)) 32 64) (concat (extract (mul (leanSignExtend (extract v_13191 128 160) 64) (leanSignExtend (extract v_13195 128 160) 64)) 32 64) (concat (extract (mul (leanSignExtend (extract v_13191 160 192) 64) (leanSignExtend (extract v_13195 160 192) 64)) 32 64) (concat (extract (mul (leanSignExtend (extract v_13191 192 224) 64) (leanSignExtend (extract v_13195 192 224) 64)) 32 64) (extract (mul (leanSignExtend (extract v_13191 224 256) 64) (leanSignExtend (extract v_13195 224 256) 64)) 32 64))))))));
      pure ()
    pat_end
