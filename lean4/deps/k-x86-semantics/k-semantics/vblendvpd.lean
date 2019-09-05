def vblendvpd1 : instruction :=
  definst "vblendvpd" $ do
    pattern fun (v_2885 : reg (bv 128)) (v_2886 : reg (bv 128)) (v_2887 : reg (bv 128)) (v_2888 : reg (bv 128)) => do
      v_5328 <- getRegister v_2885;
      v_5330 <- getRegister v_2887;
      v_5332 <- getRegister v_2886;
      setRegister (lhs.of_reg v_2888) (concat (mux (isBitClear v_5328 0) (extract v_5330 0 64) (extract v_5332 0 64)) (mux (isBitClear v_5328 64) (extract v_5330 64 128) (extract v_5332 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2897 : reg (bv 256)) (v_2898 : reg (bv 256)) (v_2899 : reg (bv 256)) (v_2900 : reg (bv 256)) => do
      v_5347 <- getRegister v_2897;
      v_5349 <- getRegister v_2899;
      v_5351 <- getRegister v_2898;
      setRegister (lhs.of_reg v_2900) (concat (mux (isBitClear v_5347 0) (extract v_5349 0 64) (extract v_5351 0 64)) (concat (mux (isBitClear v_5347 64) (extract v_5349 64 128) (extract v_5351 64 128)) (concat (mux (isBitClear v_5347 128) (extract v_5349 128 192) (extract v_5351 128 192)) (mux (isBitClear v_5347 192) (extract v_5349 192 256) (extract v_5351 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2879 : reg (bv 128)) (v_2878 : Mem) (v_2880 : reg (bv 128)) (v_2881 : reg (bv 128)) => do
      v_9542 <- getRegister v_2879;
      v_9544 <- getRegister v_2880;
      v_9546 <- evaluateAddress v_2878;
      v_9547 <- load v_9546 16;
      setRegister (lhs.of_reg v_2881) (concat (mux (isBitClear v_9542 0) (extract v_9544 0 64) (extract v_9547 0 64)) (mux (isBitClear v_9542 64) (extract v_9544 64 128) (extract v_9547 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2892 : reg (bv 256)) (v_2891 : Mem) (v_2893 : reg (bv 256)) (v_2894 : reg (bv 256)) => do
      v_9556 <- getRegister v_2892;
      v_9558 <- getRegister v_2893;
      v_9560 <- evaluateAddress v_2891;
      v_9561 <- load v_9560 32;
      setRegister (lhs.of_reg v_2894) (concat (mux (isBitClear v_9556 0) (extract v_9558 0 64) (extract v_9561 0 64)) (concat (mux (isBitClear v_9556 64) (extract v_9558 64 128) (extract v_9561 64 128)) (concat (mux (isBitClear v_9556 128) (extract v_9558 128 192) (extract v_9561 128 192)) (mux (isBitClear v_9556 192) (extract v_9558 192 256) (extract v_9561 192 256)))));
      pure ()
    pat_end
