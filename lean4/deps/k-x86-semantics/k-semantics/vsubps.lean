def vsubps1 : instruction :=
  definst "vsubps" $ do
    pattern fun (v_3102 : reg (bv 128)) (v_3103 : reg (bv 128)) (v_3104 : reg (bv 128)) => do
      v_7158 <- getRegister v_3103;
      v_7161 <- getRegister v_3102;
      setRegister (lhs.of_reg v_3104) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7158 0 32) 24 8) (MInt2Float (extract v_7161 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7158 32 64) 24 8) (MInt2Float (extract v_7161 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7158 64 96) 24 8) (MInt2Float (extract v_7161 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7158 96 128) 24 8) (MInt2Float (extract v_7161 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3113 : reg (bv 256)) (v_3114 : reg (bv 256)) (v_3115 : reg (bv 256)) => do
      v_7193 <- getRegister v_3114;
      v_7196 <- getRegister v_3113;
      setRegister (lhs.of_reg v_3115) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7193 0 32) 24 8) (MInt2Float (extract v_7196 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7193 32 64) 24 8) (MInt2Float (extract v_7196 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7193 64 96) 24 8) (MInt2Float (extract v_7196 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7193 96 128) 24 8) (MInt2Float (extract v_7196 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7193 128 160) 24 8) (MInt2Float (extract v_7196 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7193 160 192) 24 8) (MInt2Float (extract v_7196 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7193 192 224) 24 8) (MInt2Float (extract v_7196 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7193 224 256) 24 8) (MInt2Float (extract v_7196 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3096 : Mem) (v_3097 : reg (bv 128)) (v_3098 : reg (bv 128)) => do
      v_13076 <- getRegister v_3097;
      v_13079 <- evaluateAddress v_3096;
      v_13080 <- load v_13079 16;
      setRegister (lhs.of_reg v_3098) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13076 0 32) 24 8) (MInt2Float (extract v_13080 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13076 32 64) 24 8) (MInt2Float (extract v_13080 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13076 64 96) 24 8) (MInt2Float (extract v_13080 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13076 96 128) 24 8) (MInt2Float (extract v_13080 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3107 : Mem) (v_3108 : reg (bv 256)) (v_3109 : reg (bv 256)) => do
      v_13107 <- getRegister v_3108;
      v_13110 <- evaluateAddress v_3107;
      v_13111 <- load v_13110 32;
      setRegister (lhs.of_reg v_3109) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13107 0 32) 24 8) (MInt2Float (extract v_13111 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13107 32 64) 24 8) (MInt2Float (extract v_13111 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13107 64 96) 24 8) (MInt2Float (extract v_13111 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13107 96 128) 24 8) (MInt2Float (extract v_13111 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13107 128 160) 24 8) (MInt2Float (extract v_13111 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13107 160 192) 24 8) (MInt2Float (extract v_13111 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13107 192 224) 24 8) (MInt2Float (extract v_13111 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13107 224 256) 24 8) (MInt2Float (extract v_13111 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
