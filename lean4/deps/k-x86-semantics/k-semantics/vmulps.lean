def vmulps1 : instruction :=
  definst "vmulps" $ do
    pattern fun (v_3155 : reg (bv 128)) (v_3156 : reg (bv 128)) (v_3157 : reg (bv 128)) => do
      v_5210 <- getRegister v_3156;
      v_5213 <- getRegister v_3155;
      setRegister (lhs.of_reg v_3157) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5210 0 32) 24 8) (MInt2Float (extract v_5213 0 32) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5210 32 64) 24 8) (MInt2Float (extract v_5213 32 64) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5210 64 96) 24 8) (MInt2Float (extract v_5213 64 96) 24 8)) 32) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5210 96 128) 24 8) (MInt2Float (extract v_5213 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3167 : reg (bv 256)) (v_3168 : reg (bv 256)) (v_3169 : reg (bv 256)) => do
      v_5245 <- getRegister v_3168;
      v_5248 <- getRegister v_3167;
      setRegister (lhs.of_reg v_3169) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5245 0 32) 24 8) (MInt2Float (extract v_5248 0 32) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5245 32 64) 24 8) (MInt2Float (extract v_5248 32 64) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5245 64 96) 24 8) (MInt2Float (extract v_5248 64 96) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5245 96 128) 24 8) (MInt2Float (extract v_5248 96 128) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5245 128 160) 24 8) (MInt2Float (extract v_5248 128 160) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5245 160 192) 24 8) (MInt2Float (extract v_5248 160 192) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5245 192 224) 24 8) (MInt2Float (extract v_5248 192 224) 24 8)) 32) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5245 224 256) 24 8) (MInt2Float (extract v_5248 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3150 : Mem) (v_3151 : reg (bv 128)) (v_3152 : reg (bv 128)) => do
      v_10334 <- getRegister v_3151;
      v_10337 <- evaluateAddress v_3150;
      v_10338 <- load v_10337 16;
      setRegister (lhs.of_reg v_3152) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10334 0 32) 24 8) (MInt2Float (extract v_10338 0 32) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10334 32 64) 24 8) (MInt2Float (extract v_10338 32 64) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10334 64 96) 24 8) (MInt2Float (extract v_10338 64 96) 24 8)) 32) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10334 96 128) 24 8) (MInt2Float (extract v_10338 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3161 : Mem) (v_3162 : reg (bv 256)) (v_3163 : reg (bv 256)) => do
      v_10365 <- getRegister v_3162;
      v_10368 <- evaluateAddress v_3161;
      v_10369 <- load v_10368 32;
      setRegister (lhs.of_reg v_3163) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10365 0 32) 24 8) (MInt2Float (extract v_10369 0 32) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10365 32 64) 24 8) (MInt2Float (extract v_10369 32 64) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10365 64 96) 24 8) (MInt2Float (extract v_10369 64 96) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10365 96 128) 24 8) (MInt2Float (extract v_10369 96 128) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10365 128 160) 24 8) (MInt2Float (extract v_10369 128 160) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10365 160 192) 24 8) (MInt2Float (extract v_10369 160 192) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10365 192 224) 24 8) (MInt2Float (extract v_10369 192 224) 24 8)) 32) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10365 224 256) 24 8) (MInt2Float (extract v_10369 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
