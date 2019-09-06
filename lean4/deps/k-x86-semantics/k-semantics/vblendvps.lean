def vblendvps1 : instruction :=
  definst "vblendvps" $ do
    pattern fun (v_2938 : reg (bv 128)) (v_2939 : reg (bv 128)) (v_2940 : reg (bv 128)) (v_2941 : reg (bv 128)) => do
      v_5403 <- getRegister v_2938;
      v_5405 <- getRegister v_2940;
      v_5407 <- getRegister v_2939;
      setRegister (lhs.of_reg v_2941) (concat (mux (isBitClear v_5403 0) (extract v_5405 0 32) (extract v_5407 0 32)) (concat (mux (isBitClear v_5403 32) (extract v_5405 32 64) (extract v_5407 32 64)) (concat (mux (isBitClear v_5403 64) (extract v_5405 64 96) (extract v_5407 64 96)) (mux (isBitClear v_5403 96) (extract v_5405 96 128) (extract v_5407 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2948 : reg (bv 256)) (v_2949 : reg (bv 256)) (v_2950 : reg (bv 256)) (v_2951 : reg (bv 256)) => do
      v_5432 <- getRegister v_2948;
      v_5434 <- getRegister v_2950;
      v_5436 <- getRegister v_2949;
      setRegister (lhs.of_reg v_2951) (concat (mux (isBitClear v_5432 0) (extract v_5434 0 32) (extract v_5436 0 32)) (concat (mux (isBitClear v_5432 32) (extract v_5434 32 64) (extract v_5436 32 64)) (concat (mux (isBitClear v_5432 64) (extract v_5434 64 96) (extract v_5436 64 96)) (concat (mux (isBitClear v_5432 96) (extract v_5434 96 128) (extract v_5436 96 128)) (concat (mux (isBitClear v_5432 128) (extract v_5434 128 160) (extract v_5436 128 160)) (concat (mux (isBitClear v_5432 160) (extract v_5434 160 192) (extract v_5436 160 192)) (concat (mux (isBitClear v_5432 192) (extract v_5434 192 224) (extract v_5436 192 224)) (mux (isBitClear v_5432 224) (extract v_5434 224 256) (extract v_5436 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_2932 : reg (bv 128)) (v_2929 : Mem) (v_2933 : reg (bv 128)) (v_2934 : reg (bv 128)) => do
      v_9607 <- getRegister v_2932;
      v_9609 <- getRegister v_2933;
      v_9611 <- evaluateAddress v_2929;
      v_9612 <- load v_9611 16;
      setRegister (lhs.of_reg v_2934) (concat (mux (isBitClear v_9607 0) (extract v_9609 0 32) (extract v_9612 0 32)) (concat (mux (isBitClear v_9607 32) (extract v_9609 32 64) (extract v_9612 32 64)) (concat (mux (isBitClear v_9607 64) (extract v_9609 64 96) (extract v_9612 64 96)) (mux (isBitClear v_9607 96) (extract v_9609 96 128) (extract v_9612 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2943 : reg (bv 256)) (v_2942 : Mem) (v_2944 : reg (bv 256)) (v_2945 : reg (bv 256)) => do
      v_9631 <- getRegister v_2943;
      v_9633 <- getRegister v_2944;
      v_9635 <- evaluateAddress v_2942;
      v_9636 <- load v_9635 32;
      setRegister (lhs.of_reg v_2945) (concat (mux (isBitClear v_9631 0) (extract v_9633 0 32) (extract v_9636 0 32)) (concat (mux (isBitClear v_9631 32) (extract v_9633 32 64) (extract v_9636 32 64)) (concat (mux (isBitClear v_9631 64) (extract v_9633 64 96) (extract v_9636 64 96)) (concat (mux (isBitClear v_9631 96) (extract v_9633 96 128) (extract v_9636 96 128)) (concat (mux (isBitClear v_9631 128) (extract v_9633 128 160) (extract v_9636 128 160)) (concat (mux (isBitClear v_9631 160) (extract v_9633 160 192) (extract v_9636 160 192)) (concat (mux (isBitClear v_9631 192) (extract v_9633 192 224) (extract v_9636 192 224)) (mux (isBitClear v_9631 224) (extract v_9633 224 256) (extract v_9636 224 256)))))))));
      pure ()
    pat_end
