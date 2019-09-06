def vpmuldq1 : instruction :=
  definst "vpmuldq" $ do
    pattern fun (v_2900 : reg (bv 128)) (v_2901 : reg (bv 128)) (v_2902 : reg (bv 128)) => do
      v_6012 <- getRegister v_2901;
      v_6015 <- getRegister v_2900;
      setRegister (lhs.of_reg v_2902) (concat (mul (sext (extract v_6012 32 64) 64) (sext (extract v_6015 32 64) 64)) (mul (sext (extract v_6012 96 128) 64) (sext (extract v_6015 96 128) 64)));
      pure ()
    pat_end;
    pattern fun (v_2911 : reg (bv 256)) (v_2912 : reg (bv 256)) (v_2913 : reg (bv 256)) => do
      v_6031 <- getRegister v_2912;
      v_6034 <- getRegister v_2911;
      setRegister (lhs.of_reg v_2913) (concat (mul (sext (extract v_6031 32 64) 64) (sext (extract v_6034 32 64) 64)) (concat (mul (sext (extract v_6031 96 128) 64) (sext (extract v_6034 96 128) 64)) (concat (mul (sext (extract v_6031 160 192) 64) (sext (extract v_6034 160 192) 64)) (mul (sext (extract v_6031 224 256) 64) (sext (extract v_6034 224 256) 64)))));
      pure ()
    pat_end;
    pattern fun (v_2894 : Mem) (v_2895 : reg (bv 128)) (v_2896 : reg (bv 128)) => do
      v_12370 <- getRegister v_2895;
      v_12373 <- evaluateAddress v_2894;
      v_12374 <- load v_12373 16;
      setRegister (lhs.of_reg v_2896) (concat (mul (sext (extract v_12370 32 64) 64) (sext (extract v_12374 32 64) 64)) (mul (sext (extract v_12370 96 128) 64) (sext (extract v_12374 96 128) 64)));
      pure ()
    pat_end;
    pattern fun (v_2905 : Mem) (v_2906 : reg (bv 256)) (v_2907 : reg (bv 256)) => do
      v_12385 <- getRegister v_2906;
      v_12388 <- evaluateAddress v_2905;
      v_12389 <- load v_12388 32;
      setRegister (lhs.of_reg v_2907) (concat (mul (sext (extract v_12385 32 64) 64) (sext (extract v_12389 32 64) 64)) (concat (mul (sext (extract v_12385 96 128) 64) (sext (extract v_12389 96 128) 64)) (concat (mul (sext (extract v_12385 160 192) 64) (sext (extract v_12389 160 192) 64)) (mul (sext (extract v_12385 224 256) 64) (sext (extract v_12389 224 256) 64)))));
      pure ()
    pat_end
