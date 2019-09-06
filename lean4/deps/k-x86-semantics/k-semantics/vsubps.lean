def vsubps1 : instruction :=
  definst "vsubps" $ do
    pattern fun (v_3129 : reg (bv 128)) (v_3130 : reg (bv 128)) (v_3131 : reg (bv 128)) => do
      v_7185 <- getRegister v_3130;
      v_7188 <- getRegister v_3129;
      setRegister (lhs.of_reg v_3131) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7185 0 32) 24 8) (MInt2Float (extract v_7188 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7185 32 64) 24 8) (MInt2Float (extract v_7188 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7185 64 96) 24 8) (MInt2Float (extract v_7188 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7185 96 128) 24 8) (MInt2Float (extract v_7188 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3140 : reg (bv 256)) (v_3141 : reg (bv 256)) (v_3142 : reg (bv 256)) => do
      v_7220 <- getRegister v_3141;
      v_7223 <- getRegister v_3140;
      setRegister (lhs.of_reg v_3142) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7220 0 32) 24 8) (MInt2Float (extract v_7223 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7220 32 64) 24 8) (MInt2Float (extract v_7223 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7220 64 96) 24 8) (MInt2Float (extract v_7223 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7220 96 128) 24 8) (MInt2Float (extract v_7223 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7220 128 160) 24 8) (MInt2Float (extract v_7223 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7220 160 192) 24 8) (MInt2Float (extract v_7223 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7220 192 224) 24 8) (MInt2Float (extract v_7223 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7220 224 256) 24 8) (MInt2Float (extract v_7223 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3123 : Mem) (v_3124 : reg (bv 128)) (v_3125 : reg (bv 128)) => do
      v_13103 <- getRegister v_3124;
      v_13106 <- evaluateAddress v_3123;
      v_13107 <- load v_13106 16;
      setRegister (lhs.of_reg v_3125) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13103 0 32) 24 8) (MInt2Float (extract v_13107 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13103 32 64) 24 8) (MInt2Float (extract v_13107 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13103 64 96) 24 8) (MInt2Float (extract v_13107 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13103 96 128) 24 8) (MInt2Float (extract v_13107 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3134 : Mem) (v_3135 : reg (bv 256)) (v_3136 : reg (bv 256)) => do
      v_13134 <- getRegister v_3135;
      v_13137 <- evaluateAddress v_3134;
      v_13138 <- load v_13137 32;
      setRegister (lhs.of_reg v_3136) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13134 0 32) 24 8) (MInt2Float (extract v_13138 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13134 32 64) 24 8) (MInt2Float (extract v_13138 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13134 64 96) 24 8) (MInt2Float (extract v_13138 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13134 96 128) 24 8) (MInt2Float (extract v_13138 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13134 128 160) 24 8) (MInt2Float (extract v_13138 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13134 160 192) 24 8) (MInt2Float (extract v_13138 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13134 192 224) 24 8) (MInt2Float (extract v_13138 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13134 224 256) 24 8) (MInt2Float (extract v_13138 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
