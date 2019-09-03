def vfmsubadd132ps1 : instruction :=
  definst "vfmsubadd132ps" $ do
    pattern fun (v_2968 : reg (bv 128)) (v_2969 : reg (bv 128)) (v_2970 : reg (bv 128)) => do
      v_6214 <- getRegister v_2970;
      v_6217 <- getRegister v_2968;
      v_6221 <- getRegister v_2969;
      setRegister (lhs.of_reg v_2970) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6214 0 32) 24 8) (MInt2Float (extract v_6217 0 32) 24 8)) (MInt2Float (extract v_6221 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6214 32 64) 24 8) (MInt2Float (extract v_6217 32 64) 24 8)) (MInt2Float (extract v_6221 32 64) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6214 64 96) 24 8) (MInt2Float (extract v_6217 64 96) 24 8)) (MInt2Float (extract v_6221 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6214 96 128) 24 8) (MInt2Float (extract v_6217 96 128) 24 8)) (MInt2Float (extract v_6221 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2980 : reg (bv 256)) (v_2981 : reg (bv 256)) (v_2982 : reg (bv 256)) => do
      v_6262 <- getRegister v_2982;
      v_6265 <- getRegister v_2980;
      v_6269 <- getRegister v_2981;
      setRegister (lhs.of_reg v_2982) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6262 0 32) 24 8) (MInt2Float (extract v_6265 0 32) 24 8)) (MInt2Float (extract v_6269 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6262 32 64) 24 8) (MInt2Float (extract v_6265 32 64) 24 8)) (MInt2Float (extract v_6269 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6262 64 96) 24 8) (MInt2Float (extract v_6265 64 96) 24 8)) (MInt2Float (extract v_6269 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6262 96 128) 24 8) (MInt2Float (extract v_6265 96 128) 24 8)) (MInt2Float (extract v_6269 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6262 128 160) 24 8) (MInt2Float (extract v_6265 128 160) 24 8)) (MInt2Float (extract v_6269 128 160) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6262 160 192) 24 8) (MInt2Float (extract v_6265 160 192) 24 8)) (MInt2Float (extract v_6269 160 192) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6262 192 224) 24 8) (MInt2Float (extract v_6265 192 224) 24 8)) (MInt2Float (extract v_6269 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6262 224 256) 24 8) (MInt2Float (extract v_6265 224 256) 24 8)) (MInt2Float (extract v_6269 224 256) 24 8)) 32)))));
      pure ()
    pat_end;
    pattern fun (v_2965 : Mem) (v_2963 : reg (bv 128)) (v_2964 : reg (bv 128)) => do
      v_12019 <- getRegister v_2964;
      v_12022 <- evaluateAddress v_2965;
      v_12023 <- load v_12022 16;
      v_12027 <- getRegister v_2963;
      setRegister (lhs.of_reg v_2964) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12019 0 32) 24 8) (MInt2Float (extract v_12023 0 32) 24 8)) (MInt2Float (extract v_12027 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12019 32 64) 24 8) (MInt2Float (extract v_12023 32 64) 24 8)) (MInt2Float (extract v_12027 32 64) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12019 64 96) 24 8) (MInt2Float (extract v_12023 64 96) 24 8)) (MInt2Float (extract v_12027 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12019 96 128) 24 8) (MInt2Float (extract v_12023 96 128) 24 8)) (MInt2Float (extract v_12027 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2974 : Mem) (v_2975 : reg (bv 256)) (v_2976 : reg (bv 256)) => do
      v_12063 <- getRegister v_2976;
      v_12066 <- evaluateAddress v_2974;
      v_12067 <- load v_12066 32;
      v_12071 <- getRegister v_2975;
      setRegister (lhs.of_reg v_2976) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12063 0 32) 24 8) (MInt2Float (extract v_12067 0 32) 24 8)) (MInt2Float (extract v_12071 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12063 32 64) 24 8) (MInt2Float (extract v_12067 32 64) 24 8)) (MInt2Float (extract v_12071 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12063 64 96) 24 8) (MInt2Float (extract v_12067 64 96) 24 8)) (MInt2Float (extract v_12071 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12063 96 128) 24 8) (MInt2Float (extract v_12067 96 128) 24 8)) (MInt2Float (extract v_12071 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12063 128 160) 24 8) (MInt2Float (extract v_12067 128 160) 24 8)) (MInt2Float (extract v_12071 128 160) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12063 160 192) 24 8) (MInt2Float (extract v_12067 160 192) 24 8)) (MInt2Float (extract v_12071 160 192) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12063 192 224) 24 8) (MInt2Float (extract v_12067 192 224) 24 8)) (MInt2Float (extract v_12071 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12063 224 256) 24 8) (MInt2Float (extract v_12067 224 256) 24 8)) (MInt2Float (extract v_12071 224 256) 24 8)) 32)))));
      pure ()
    pat_end
