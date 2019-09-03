def vmulps1 : instruction :=
  definst "vmulps" $ do
    pattern fun (v_3092 : reg (bv 128)) (v_3093 : reg (bv 128)) (v_3094 : reg (bv 128)) => do
      v_5152 <- getRegister v_3093;
      v_5155 <- getRegister v_3092;
      setRegister (lhs.of_reg v_3094) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5152 0 32) 24 8) (MInt2Float (extract v_5155 0 32) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5152 32 64) 24 8) (MInt2Float (extract v_5155 32 64) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5152 64 96) 24 8) (MInt2Float (extract v_5155 64 96) 24 8)) 32) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5152 96 128) 24 8) (MInt2Float (extract v_5155 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3103 : reg (bv 256)) (v_3104 : reg (bv 256)) (v_3105 : reg (bv 256)) => do
      v_5187 <- getRegister v_3104;
      v_5190 <- getRegister v_3103;
      setRegister (lhs.of_reg v_3105) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5187 0 32) 24 8) (MInt2Float (extract v_5190 0 32) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5187 32 64) 24 8) (MInt2Float (extract v_5190 32 64) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5187 64 96) 24 8) (MInt2Float (extract v_5190 64 96) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5187 96 128) 24 8) (MInt2Float (extract v_5190 96 128) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5187 128 160) 24 8) (MInt2Float (extract v_5190 128 160) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5187 160 192) 24 8) (MInt2Float (extract v_5190 160 192) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5187 192 224) 24 8) (MInt2Float (extract v_5190 192 224) 24 8)) 32) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5187 224 256) 24 8) (MInt2Float (extract v_5190 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3086 : Mem) (v_3087 : reg (bv 128)) (v_3088 : reg (bv 128)) => do
      v_10468 <- getRegister v_3087;
      v_10471 <- evaluateAddress v_3086;
      v_10472 <- load v_10471 16;
      setRegister (lhs.of_reg v_3088) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10468 0 32) 24 8) (MInt2Float (extract v_10472 0 32) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10468 32 64) 24 8) (MInt2Float (extract v_10472 32 64) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10468 64 96) 24 8) (MInt2Float (extract v_10472 64 96) 24 8)) 32) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10468 96 128) 24 8) (MInt2Float (extract v_10472 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3097 : Mem) (v_3098 : reg (bv 256)) (v_3099 : reg (bv 256)) => do
      v_10499 <- getRegister v_3098;
      v_10502 <- evaluateAddress v_3097;
      v_10503 <- load v_10502 32;
      setRegister (lhs.of_reg v_3099) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10499 0 32) 24 8) (MInt2Float (extract v_10503 0 32) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10499 32 64) 24 8) (MInt2Float (extract v_10503 32 64) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10499 64 96) 24 8) (MInt2Float (extract v_10503 64 96) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10499 96 128) 24 8) (MInt2Float (extract v_10503 96 128) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10499 128 160) 24 8) (MInt2Float (extract v_10503 128 160) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10499 160 192) 24 8) (MInt2Float (extract v_10503 160 192) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10499 192 224) 24 8) (MInt2Float (extract v_10503 192 224) 24 8)) 32) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10499 224 256) 24 8) (MInt2Float (extract v_10503 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
