def vpmulld1 : instruction :=
  definst "vpmulld" $ do
    pattern fun (v_2988 : reg (bv 128)) (v_2989 : reg (bv 128)) (v_2990 : reg (bv 128)) => do
      v_6656 <- getRegister v_2989;
      v_6659 <- getRegister v_2988;
      setRegister (lhs.of_reg v_2990) (concat (extract (mul (sext (extract v_6656 0 32) 64) (sext (extract v_6659 0 32) 64)) 32 64) (concat (extract (mul (sext (extract v_6656 32 64) 64) (sext (extract v_6659 32 64) 64)) 32 64) (concat (extract (mul (sext (extract v_6656 64 96) 64) (sext (extract v_6659 64 96) 64)) 32 64) (extract (mul (sext (extract v_6656 96 128) 64) (sext (extract v_6659 96 128) 64)) 32 64))));
      pure ()
    pat_end;
    pattern fun (v_2999 : reg (bv 256)) (v_3000 : reg (bv 256)) (v_3001 : reg (bv 256)) => do
      v_6691 <- getRegister v_3000;
      v_6694 <- getRegister v_2999;
      setRegister (lhs.of_reg v_3001) (concat (extract (mul (sext (extract v_6691 0 32) 64) (sext (extract v_6694 0 32) 64)) 32 64) (concat (extract (mul (sext (extract v_6691 32 64) 64) (sext (extract v_6694 32 64) 64)) 32 64) (concat (extract (mul (sext (extract v_6691 64 96) 64) (sext (extract v_6694 64 96) 64)) 32 64) (concat (extract (mul (sext (extract v_6691 96 128) 64) (sext (extract v_6694 96 128) 64)) 32 64) (concat (extract (mul (sext (extract v_6691 128 160) 64) (sext (extract v_6694 128 160) 64)) 32 64) (concat (extract (mul (sext (extract v_6691 160 192) 64) (sext (extract v_6694 160 192) 64)) 32 64) (concat (extract (mul (sext (extract v_6691 192 224) 64) (sext (extract v_6694 192 224) 64)) 32 64) (extract (mul (sext (extract v_6691 224 256) 64) (sext (extract v_6694 224 256) 64)) 32 64))))))));
      pure ()
    pat_end;
    pattern fun (v_2982 : Mem) (v_2983 : reg (bv 128)) (v_2984 : reg (bv 128)) => do
      v_12982 <- getRegister v_2983;
      v_12985 <- evaluateAddress v_2982;
      v_12986 <- load v_12985 16;
      setRegister (lhs.of_reg v_2984) (concat (extract (mul (sext (extract v_12982 0 32) 64) (sext (extract v_12986 0 32) 64)) 32 64) (concat (extract (mul (sext (extract v_12982 32 64) 64) (sext (extract v_12986 32 64) 64)) 32 64) (concat (extract (mul (sext (extract v_12982 64 96) 64) (sext (extract v_12986 64 96) 64)) 32 64) (extract (mul (sext (extract v_12982 96 128) 64) (sext (extract v_12986 96 128) 64)) 32 64))));
      pure ()
    pat_end;
    pattern fun (v_2993 : Mem) (v_2994 : reg (bv 256)) (v_2995 : reg (bv 256)) => do
      v_13013 <- getRegister v_2994;
      v_13016 <- evaluateAddress v_2993;
      v_13017 <- load v_13016 32;
      setRegister (lhs.of_reg v_2995) (concat (extract (mul (sext (extract v_13013 0 32) 64) (sext (extract v_13017 0 32) 64)) 32 64) (concat (extract (mul (sext (extract v_13013 32 64) 64) (sext (extract v_13017 32 64) 64)) 32 64) (concat (extract (mul (sext (extract v_13013 64 96) 64) (sext (extract v_13017 64 96) 64)) 32 64) (concat (extract (mul (sext (extract v_13013 96 128) 64) (sext (extract v_13017 96 128) 64)) 32 64) (concat (extract (mul (sext (extract v_13013 128 160) 64) (sext (extract v_13017 128 160) 64)) 32 64) (concat (extract (mul (sext (extract v_13013 160 192) 64) (sext (extract v_13017 160 192) 64)) 32 64) (concat (extract (mul (sext (extract v_13013 192 224) 64) (sext (extract v_13017 192 224) 64)) 32 64) (extract (mul (sext (extract v_13013 224 256) 64) (sext (extract v_13017 224 256) 64)) 32 64))))))));
      pure ()
    pat_end
