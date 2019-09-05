def vfmsubadd213ps1 : instruction :=
  definst "vfmsubadd213ps" $ do
    pattern fun (v_3077 : reg (bv 128)) (v_3078 : reg (bv 128)) (v_3079 : reg (bv 128)) => do
      v_6493 <- getRegister v_3078;
      v_6496 <- getRegister v_3079;
      v_6500 <- getRegister v_3077;
      setRegister (lhs.of_reg v_3079) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6493 0 32) 24 8) (MInt2Float (extract v_6496 0 32) 24 8)) (MInt2Float (extract v_6500 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6493 32 64) 24 8) (MInt2Float (extract v_6496 32 64) 24 8)) (MInt2Float (extract v_6500 32 64) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6493 64 96) 24 8) (MInt2Float (extract v_6496 64 96) 24 8)) (MInt2Float (extract v_6500 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6493 96 128) 24 8) (MInt2Float (extract v_6496 96 128) 24 8)) (MInt2Float (extract v_6500 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_3087 : reg (bv 256)) (v_3088 : reg (bv 256)) (v_3089 : reg (bv 256)) => do
      v_6541 <- getRegister v_3088;
      v_6544 <- getRegister v_3089;
      v_6548 <- getRegister v_3087;
      setRegister (lhs.of_reg v_3089) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6541 0 32) 24 8) (MInt2Float (extract v_6544 0 32) 24 8)) (MInt2Float (extract v_6548 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6541 32 64) 24 8) (MInt2Float (extract v_6544 32 64) 24 8)) (MInt2Float (extract v_6548 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6541 64 96) 24 8) (MInt2Float (extract v_6544 64 96) 24 8)) (MInt2Float (extract v_6548 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6541 96 128) 24 8) (MInt2Float (extract v_6544 96 128) 24 8)) (MInt2Float (extract v_6548 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6541 128 160) 24 8) (MInt2Float (extract v_6544 128 160) 24 8)) (MInt2Float (extract v_6548 128 160) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6541 160 192) 24 8) (MInt2Float (extract v_6544 160 192) 24 8)) (MInt2Float (extract v_6548 160 192) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6541 192 224) 24 8) (MInt2Float (extract v_6544 192 224) 24 8)) (MInt2Float (extract v_6548 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6541 224 256) 24 8) (MInt2Float (extract v_6544 224 256) 24 8)) (MInt2Float (extract v_6548 224 256) 24 8)) 32)))));
      pure ()
    pat_end;
    pattern fun (v_3071 : Mem) (v_3072 : reg (bv 128)) (v_3073 : reg (bv 128)) => do
      v_12299 <- getRegister v_3072;
      v_12302 <- getRegister v_3073;
      v_12306 <- evaluateAddress v_3071;
      v_12307 <- load v_12306 16;
      setRegister (lhs.of_reg v_3073) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12299 0 32) 24 8) (MInt2Float (extract v_12302 0 32) 24 8)) (MInt2Float (extract v_12307 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12299 32 64) 24 8) (MInt2Float (extract v_12302 32 64) 24 8)) (MInt2Float (extract v_12307 32 64) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12299 64 96) 24 8) (MInt2Float (extract v_12302 64 96) 24 8)) (MInt2Float (extract v_12307 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12299 96 128) 24 8) (MInt2Float (extract v_12302 96 128) 24 8)) (MInt2Float (extract v_12307 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_3082 : Mem) (v_3083 : reg (bv 256)) (v_3084 : reg (bv 256)) => do
      v_12343 <- getRegister v_3083;
      v_12346 <- getRegister v_3084;
      v_12350 <- evaluateAddress v_3082;
      v_12351 <- load v_12350 32;
      setRegister (lhs.of_reg v_3084) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12343 0 32) 24 8) (MInt2Float (extract v_12346 0 32) 24 8)) (MInt2Float (extract v_12351 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12343 32 64) 24 8) (MInt2Float (extract v_12346 32 64) 24 8)) (MInt2Float (extract v_12351 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12343 64 96) 24 8) (MInt2Float (extract v_12346 64 96) 24 8)) (MInt2Float (extract v_12351 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12343 96 128) 24 8) (MInt2Float (extract v_12346 96 128) 24 8)) (MInt2Float (extract v_12351 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12343 128 160) 24 8) (MInt2Float (extract v_12346 128 160) 24 8)) (MInt2Float (extract v_12351 128 160) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12343 160 192) 24 8) (MInt2Float (extract v_12346 160 192) 24 8)) (MInt2Float (extract v_12351 160 192) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12343 192 224) 24 8) (MInt2Float (extract v_12346 192 224) 24 8)) (MInt2Float (extract v_12351 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12343 224 256) 24 8) (MInt2Float (extract v_12346 224 256) 24 8)) (MInt2Float (extract v_12351 224 256) 24 8)) 32)))));
      pure ()
    pat_end
