def vsubps1 : instruction :=
  definst "vsubps" $ do
    pattern fun (v_2383 : reg (bv 128)) (v_2384 : reg (bv 128)) (v_2385 : reg (bv 128)) => do
      v_3259 <- getRegister v_2384;
      v_3262 <- getRegister v_2383;
      setRegister (lhs.of_reg v_2385) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_3259 0 32) 24 8) (MInt2Float (extract v_3262 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_3259 32 64) 24 8) (MInt2Float (extract v_3262 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_3259 64 96) 24 8) (MInt2Float (extract v_3262 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_3259 96 128) 24 8) (MInt2Float (extract v_3262 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2395 : reg (bv 256)) (v_2396 : reg (bv 256)) (v_2397 : reg (bv 256)) => do
      v_3294 <- getRegister v_2396;
      v_3297 <- getRegister v_2395;
      setRegister (lhs.of_reg v_2397) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_3294 0 32) 24 8) (MInt2Float (extract v_3297 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_3294 32 64) 24 8) (MInt2Float (extract v_3297 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_3294 64 96) 24 8) (MInt2Float (extract v_3297 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_3294 96 128) 24 8) (MInt2Float (extract v_3297 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_3294 128 160) 24 8) (MInt2Float (extract v_3297 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_3294 160 192) 24 8) (MInt2Float (extract v_3297 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_3294 192 224) 24 8) (MInt2Float (extract v_3297 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_3294 224 256) 24 8) (MInt2Float (extract v_3297 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2378 : Mem) (v_2379 : reg (bv 128)) (v_2380 : reg (bv 128)) => do
      v_6548 <- getRegister v_2379;
      v_6551 <- evaluateAddress v_2378;
      v_6552 <- load v_6551 16;
      setRegister (lhs.of_reg v_2380) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6548 0 32) 24 8) (MInt2Float (extract v_6552 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6548 32 64) 24 8) (MInt2Float (extract v_6552 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6548 64 96) 24 8) (MInt2Float (extract v_6552 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6548 96 128) 24 8) (MInt2Float (extract v_6552 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2389 : Mem) (v_2390 : reg (bv 256)) (v_2391 : reg (bv 256)) => do
      v_6579 <- getRegister v_2390;
      v_6582 <- evaluateAddress v_2389;
      v_6583 <- load v_6582 32;
      setRegister (lhs.of_reg v_2391) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6579 0 32) 24 8) (MInt2Float (extract v_6583 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6579 32 64) 24 8) (MInt2Float (extract v_6583 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6579 64 96) 24 8) (MInt2Float (extract v_6583 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6579 96 128) 24 8) (MInt2Float (extract v_6583 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6579 128 160) 24 8) (MInt2Float (extract v_6583 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6579 160 192) 24 8) (MInt2Float (extract v_6583 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6579 192 224) 24 8) (MInt2Float (extract v_6583 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6579 224 256) 24 8) (MInt2Float (extract v_6583 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
