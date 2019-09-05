def vpmulld1 : instruction :=
  definst "vpmulld" $ do
    pattern fun (v_2961 : reg (bv 128)) (v_2962 : reg (bv 128)) (v_2963 : reg (bv 128)) => do
      v_6629 <- getRegister v_2962;
      v_6632 <- getRegister v_2961;
      setRegister (lhs.of_reg v_2963) (concat (extract (mul (sext (extract v_6629 0 32) 64) (sext (extract v_6632 0 32) 64)) 32 64) (concat (extract (mul (sext (extract v_6629 32 64) 64) (sext (extract v_6632 32 64) 64)) 32 64) (concat (extract (mul (sext (extract v_6629 64 96) 64) (sext (extract v_6632 64 96) 64)) 32 64) (extract (mul (sext (extract v_6629 96 128) 64) (sext (extract v_6632 96 128) 64)) 32 64))));
      pure ()
    pat_end;
    pattern fun (v_2972 : reg (bv 256)) (v_2973 : reg (bv 256)) (v_2974 : reg (bv 256)) => do
      v_6664 <- getRegister v_2973;
      v_6667 <- getRegister v_2972;
      setRegister (lhs.of_reg v_2974) (concat (extract (mul (sext (extract v_6664 0 32) 64) (sext (extract v_6667 0 32) 64)) 32 64) (concat (extract (mul (sext (extract v_6664 32 64) 64) (sext (extract v_6667 32 64) 64)) 32 64) (concat (extract (mul (sext (extract v_6664 64 96) 64) (sext (extract v_6667 64 96) 64)) 32 64) (concat (extract (mul (sext (extract v_6664 96 128) 64) (sext (extract v_6667 96 128) 64)) 32 64) (concat (extract (mul (sext (extract v_6664 128 160) 64) (sext (extract v_6667 128 160) 64)) 32 64) (concat (extract (mul (sext (extract v_6664 160 192) 64) (sext (extract v_6667 160 192) 64)) 32 64) (concat (extract (mul (sext (extract v_6664 192 224) 64) (sext (extract v_6667 192 224) 64)) 32 64) (extract (mul (sext (extract v_6664 224 256) 64) (sext (extract v_6667 224 256) 64)) 32 64))))))));
      pure ()
    pat_end;
    pattern fun (v_2955 : Mem) (v_2956 : reg (bv 128)) (v_2957 : reg (bv 128)) => do
      v_12955 <- getRegister v_2956;
      v_12958 <- evaluateAddress v_2955;
      v_12959 <- load v_12958 16;
      setRegister (lhs.of_reg v_2957) (concat (extract (mul (sext (extract v_12955 0 32) 64) (sext (extract v_12959 0 32) 64)) 32 64) (concat (extract (mul (sext (extract v_12955 32 64) 64) (sext (extract v_12959 32 64) 64)) 32 64) (concat (extract (mul (sext (extract v_12955 64 96) 64) (sext (extract v_12959 64 96) 64)) 32 64) (extract (mul (sext (extract v_12955 96 128) 64) (sext (extract v_12959 96 128) 64)) 32 64))));
      pure ()
    pat_end;
    pattern fun (v_2966 : Mem) (v_2967 : reg (bv 256)) (v_2968 : reg (bv 256)) => do
      v_12986 <- getRegister v_2967;
      v_12989 <- evaluateAddress v_2966;
      v_12990 <- load v_12989 32;
      setRegister (lhs.of_reg v_2968) (concat (extract (mul (sext (extract v_12986 0 32) 64) (sext (extract v_12990 0 32) 64)) 32 64) (concat (extract (mul (sext (extract v_12986 32 64) 64) (sext (extract v_12990 32 64) 64)) 32 64) (concat (extract (mul (sext (extract v_12986 64 96) 64) (sext (extract v_12990 64 96) 64)) 32 64) (concat (extract (mul (sext (extract v_12986 96 128) 64) (sext (extract v_12990 96 128) 64)) 32 64) (concat (extract (mul (sext (extract v_12986 128 160) 64) (sext (extract v_12990 128 160) 64)) 32 64) (concat (extract (mul (sext (extract v_12986 160 192) 64) (sext (extract v_12990 160 192) 64)) 32 64) (concat (extract (mul (sext (extract v_12986 192 224) 64) (sext (extract v_12990 192 224) 64)) 32 64) (extract (mul (sext (extract v_12986 224 256) 64) (sext (extract v_12990 224 256) 64)) 32 64))))))));
      pure ()
    pat_end
