def vpmuldq1 : instruction :=
  definst "vpmuldq" $ do
    pattern fun (v_2873 : reg (bv 128)) (v_2874 : reg (bv 128)) (v_2875 : reg (bv 128)) => do
      v_5985 <- getRegister v_2874;
      v_5988 <- getRegister v_2873;
      setRegister (lhs.of_reg v_2875) (concat (mul (sext (extract v_5985 32 64) 64) (sext (extract v_5988 32 64) 64)) (mul (sext (extract v_5985 96 128) 64) (sext (extract v_5988 96 128) 64)));
      pure ()
    pat_end;
    pattern fun (v_2884 : reg (bv 256)) (v_2885 : reg (bv 256)) (v_2886 : reg (bv 256)) => do
      v_6004 <- getRegister v_2885;
      v_6007 <- getRegister v_2884;
      setRegister (lhs.of_reg v_2886) (concat (mul (sext (extract v_6004 32 64) 64) (sext (extract v_6007 32 64) 64)) (concat (mul (sext (extract v_6004 96 128) 64) (sext (extract v_6007 96 128) 64)) (concat (mul (sext (extract v_6004 160 192) 64) (sext (extract v_6007 160 192) 64)) (mul (sext (extract v_6004 224 256) 64) (sext (extract v_6007 224 256) 64)))));
      pure ()
    pat_end;
    pattern fun (v_2867 : Mem) (v_2868 : reg (bv 128)) (v_2869 : reg (bv 128)) => do
      v_12343 <- getRegister v_2868;
      v_12346 <- evaluateAddress v_2867;
      v_12347 <- load v_12346 16;
      setRegister (lhs.of_reg v_2869) (concat (mul (sext (extract v_12343 32 64) 64) (sext (extract v_12347 32 64) 64)) (mul (sext (extract v_12343 96 128) 64) (sext (extract v_12347 96 128) 64)));
      pure ()
    pat_end;
    pattern fun (v_2878 : Mem) (v_2879 : reg (bv 256)) (v_2880 : reg (bv 256)) => do
      v_12358 <- getRegister v_2879;
      v_12361 <- evaluateAddress v_2878;
      v_12362 <- load v_12361 32;
      setRegister (lhs.of_reg v_2880) (concat (mul (sext (extract v_12358 32 64) 64) (sext (extract v_12362 32 64) 64)) (concat (mul (sext (extract v_12358 96 128) 64) (sext (extract v_12362 96 128) 64)) (concat (mul (sext (extract v_12358 160 192) 64) (sext (extract v_12362 160 192) 64)) (mul (sext (extract v_12358 224 256) 64) (sext (extract v_12362 224 256) 64)))));
      pure ()
    pat_end
