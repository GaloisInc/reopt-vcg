def vmulps1 : instruction :=
  definst "vmulps" $ do
    pattern fun (v_3180 : reg (bv 128)) (v_3181 : reg (bv 128)) (v_3182 : reg (bv 128)) => do
      v_5237 <- getRegister v_3181;
      v_5240 <- getRegister v_3180;
      setRegister (lhs.of_reg v_3182) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5237 0 32) 24 8) (MInt2Float (extract v_5240 0 32) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5237 32 64) 24 8) (MInt2Float (extract v_5240 32 64) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5237 64 96) 24 8) (MInt2Float (extract v_5240 64 96) 24 8)) 32) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5237 96 128) 24 8) (MInt2Float (extract v_5240 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3191 : reg (bv 256)) (v_3192 : reg (bv 256)) (v_3193 : reg (bv 256)) => do
      v_5272 <- getRegister v_3192;
      v_5275 <- getRegister v_3191;
      setRegister (lhs.of_reg v_3193) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5272 0 32) 24 8) (MInt2Float (extract v_5275 0 32) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5272 32 64) 24 8) (MInt2Float (extract v_5275 32 64) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5272 64 96) 24 8) (MInt2Float (extract v_5275 64 96) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5272 96 128) 24 8) (MInt2Float (extract v_5275 96 128) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5272 128 160) 24 8) (MInt2Float (extract v_5275 128 160) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5272 160 192) 24 8) (MInt2Float (extract v_5275 160 192) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5272 192 224) 24 8) (MInt2Float (extract v_5275 192 224) 24 8)) 32) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5272 224 256) 24 8) (MInt2Float (extract v_5275 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3175 : Mem) (v_3176 : reg (bv 128)) (v_3177 : reg (bv 128)) => do
      v_10361 <- getRegister v_3176;
      v_10364 <- evaluateAddress v_3175;
      v_10365 <- load v_10364 16;
      setRegister (lhs.of_reg v_3177) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10361 0 32) 24 8) (MInt2Float (extract v_10365 0 32) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10361 32 64) 24 8) (MInt2Float (extract v_10365 32 64) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10361 64 96) 24 8) (MInt2Float (extract v_10365 64 96) 24 8)) 32) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10361 96 128) 24 8) (MInt2Float (extract v_10365 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3186 : Mem) (v_3187 : reg (bv 256)) (v_3188 : reg (bv 256)) => do
      v_10392 <- getRegister v_3187;
      v_10395 <- evaluateAddress v_3186;
      v_10396 <- load v_10395 32;
      setRegister (lhs.of_reg v_3188) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10392 0 32) 24 8) (MInt2Float (extract v_10396 0 32) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10392 32 64) 24 8) (MInt2Float (extract v_10396 32 64) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10392 64 96) 24 8) (MInt2Float (extract v_10396 64 96) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10392 96 128) 24 8) (MInt2Float (extract v_10396 96 128) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10392 128 160) 24 8) (MInt2Float (extract v_10396 128 160) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10392 160 192) 24 8) (MInt2Float (extract v_10396 160 192) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10392 192 224) 24 8) (MInt2Float (extract v_10396 192 224) 24 8)) 32) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10392 224 256) 24 8) (MInt2Float (extract v_10396 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
