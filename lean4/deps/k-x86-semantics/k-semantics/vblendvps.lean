def vblendvps1 : instruction :=
  definst "vblendvps" $ do
    pattern fun (v_2911 : reg (bv 128)) (v_2912 : reg (bv 128)) (v_2913 : reg (bv 128)) (v_2914 : reg (bv 128)) => do
      v_5376 <- getRegister v_2911;
      v_5378 <- getRegister v_2913;
      v_5380 <- getRegister v_2912;
      setRegister (lhs.of_reg v_2914) (concat (mux (isBitClear v_5376 0) (extract v_5378 0 32) (extract v_5380 0 32)) (concat (mux (isBitClear v_5376 32) (extract v_5378 32 64) (extract v_5380 32 64)) (concat (mux (isBitClear v_5376 64) (extract v_5378 64 96) (extract v_5380 64 96)) (mux (isBitClear v_5376 96) (extract v_5378 96 128) (extract v_5380 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2923 : reg (bv 256)) (v_2924 : reg (bv 256)) (v_2925 : reg (bv 256)) (v_2926 : reg (bv 256)) => do
      v_5405 <- getRegister v_2923;
      v_5407 <- getRegister v_2925;
      v_5409 <- getRegister v_2924;
      setRegister (lhs.of_reg v_2926) (concat (mux (isBitClear v_5405 0) (extract v_5407 0 32) (extract v_5409 0 32)) (concat (mux (isBitClear v_5405 32) (extract v_5407 32 64) (extract v_5409 32 64)) (concat (mux (isBitClear v_5405 64) (extract v_5407 64 96) (extract v_5409 64 96)) (concat (mux (isBitClear v_5405 96) (extract v_5407 96 128) (extract v_5409 96 128)) (concat (mux (isBitClear v_5405 128) (extract v_5407 128 160) (extract v_5409 128 160)) (concat (mux (isBitClear v_5405 160) (extract v_5407 160 192) (extract v_5409 160 192)) (concat (mux (isBitClear v_5405 192) (extract v_5407 192 224) (extract v_5409 192 224)) (mux (isBitClear v_5405 224) (extract v_5407 224 256) (extract v_5409 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_2905 : reg (bv 128)) (v_2904 : Mem) (v_2906 : reg (bv 128)) (v_2907 : reg (bv 128)) => do
      v_9580 <- getRegister v_2905;
      v_9582 <- getRegister v_2906;
      v_9584 <- evaluateAddress v_2904;
      v_9585 <- load v_9584 16;
      setRegister (lhs.of_reg v_2907) (concat (mux (isBitClear v_9580 0) (extract v_9582 0 32) (extract v_9585 0 32)) (concat (mux (isBitClear v_9580 32) (extract v_9582 32 64) (extract v_9585 32 64)) (concat (mux (isBitClear v_9580 64) (extract v_9582 64 96) (extract v_9585 64 96)) (mux (isBitClear v_9580 96) (extract v_9582 96 128) (extract v_9585 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2918 : reg (bv 256)) (v_2917 : Mem) (v_2919 : reg (bv 256)) (v_2920 : reg (bv 256)) => do
      v_9604 <- getRegister v_2918;
      v_9606 <- getRegister v_2919;
      v_9608 <- evaluateAddress v_2917;
      v_9609 <- load v_9608 32;
      setRegister (lhs.of_reg v_2920) (concat (mux (isBitClear v_9604 0) (extract v_9606 0 32) (extract v_9609 0 32)) (concat (mux (isBitClear v_9604 32) (extract v_9606 32 64) (extract v_9609 32 64)) (concat (mux (isBitClear v_9604 64) (extract v_9606 64 96) (extract v_9609 64 96)) (concat (mux (isBitClear v_9604 96) (extract v_9606 96 128) (extract v_9609 96 128)) (concat (mux (isBitClear v_9604 128) (extract v_9606 128 160) (extract v_9609 128 160)) (concat (mux (isBitClear v_9604 160) (extract v_9606 160 192) (extract v_9609 160 192)) (concat (mux (isBitClear v_9604 192) (extract v_9606 192 224) (extract v_9609 192 224)) (mux (isBitClear v_9604 224) (extract v_9606 224 256) (extract v_9609 224 256)))))))));
      pure ()
    pat_end
