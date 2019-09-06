def vfmsubadd213ps1 : instruction :=
  definst "vfmsubadd213ps" $ do
    pattern fun (v_3101 : reg (bv 128)) (v_3102 : reg (bv 128)) (v_3103 : reg (bv 128)) => do
      v_6520 <- getRegister v_3102;
      v_6523 <- getRegister v_3103;
      v_6527 <- getRegister v_3101;
      setRegister (lhs.of_reg v_3103) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6520 0 32) 24 8) (MInt2Float (extract v_6523 0 32) 24 8)) (MInt2Float (extract v_6527 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6520 32 64) 24 8) (MInt2Float (extract v_6523 32 64) 24 8)) (MInt2Float (extract v_6527 32 64) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6520 64 96) 24 8) (MInt2Float (extract v_6523 64 96) 24 8)) (MInt2Float (extract v_6527 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6520 96 128) 24 8) (MInt2Float (extract v_6523 96 128) 24 8)) (MInt2Float (extract v_6527 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_3115 : reg (bv 256)) (v_3116 : reg (bv 256)) (v_3117 : reg (bv 256)) => do
      v_6568 <- getRegister v_3116;
      v_6571 <- getRegister v_3117;
      v_6575 <- getRegister v_3115;
      setRegister (lhs.of_reg v_3117) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6568 0 32) 24 8) (MInt2Float (extract v_6571 0 32) 24 8)) (MInt2Float (extract v_6575 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6568 32 64) 24 8) (MInt2Float (extract v_6571 32 64) 24 8)) (MInt2Float (extract v_6575 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6568 64 96) 24 8) (MInt2Float (extract v_6571 64 96) 24 8)) (MInt2Float (extract v_6575 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6568 96 128) 24 8) (MInt2Float (extract v_6571 96 128) 24 8)) (MInt2Float (extract v_6575 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6568 128 160) 24 8) (MInt2Float (extract v_6571 128 160) 24 8)) (MInt2Float (extract v_6575 128 160) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6568 160 192) 24 8) (MInt2Float (extract v_6571 160 192) 24 8)) (MInt2Float (extract v_6575 160 192) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6568 192 224) 24 8) (MInt2Float (extract v_6571 192 224) 24 8)) (MInt2Float (extract v_6575 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6568 224 256) 24 8) (MInt2Float (extract v_6571 224 256) 24 8)) (MInt2Float (extract v_6575 224 256) 24 8)) 32)))));
      pure ()
    pat_end;
    pattern fun (v_3098 : Mem) (v_3096 : reg (bv 128)) (v_3097 : reg (bv 128)) => do
      v_12326 <- getRegister v_3096;
      v_12329 <- getRegister v_3097;
      v_12333 <- evaluateAddress v_3098;
      v_12334 <- load v_12333 16;
      setRegister (lhs.of_reg v_3097) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12326 0 32) 24 8) (MInt2Float (extract v_12329 0 32) 24 8)) (MInt2Float (extract v_12334 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12326 32 64) 24 8) (MInt2Float (extract v_12329 32 64) 24 8)) (MInt2Float (extract v_12334 32 64) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12326 64 96) 24 8) (MInt2Float (extract v_12329 64 96) 24 8)) (MInt2Float (extract v_12334 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12326 96 128) 24 8) (MInt2Float (extract v_12329 96 128) 24 8)) (MInt2Float (extract v_12334 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_3107 : Mem) (v_3110 : reg (bv 256)) (v_3111 : reg (bv 256)) => do
      v_12370 <- getRegister v_3110;
      v_12373 <- getRegister v_3111;
      v_12377 <- evaluateAddress v_3107;
      v_12378 <- load v_12377 32;
      setRegister (lhs.of_reg v_3111) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12370 0 32) 24 8) (MInt2Float (extract v_12373 0 32) 24 8)) (MInt2Float (extract v_12378 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12370 32 64) 24 8) (MInt2Float (extract v_12373 32 64) 24 8)) (MInt2Float (extract v_12378 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12370 64 96) 24 8) (MInt2Float (extract v_12373 64 96) 24 8)) (MInt2Float (extract v_12378 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12370 96 128) 24 8) (MInt2Float (extract v_12373 96 128) 24 8)) (MInt2Float (extract v_12378 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12370 128 160) 24 8) (MInt2Float (extract v_12373 128 160) 24 8)) (MInt2Float (extract v_12378 128 160) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12370 160 192) 24 8) (MInt2Float (extract v_12373 160 192) 24 8)) (MInt2Float (extract v_12378 160 192) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12370 192 224) 24 8) (MInt2Float (extract v_12373 192 224) 24 8)) (MInt2Float (extract v_12378 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12370 224 256) 24 8) (MInt2Float (extract v_12373 224 256) 24 8)) (MInt2Float (extract v_12378 224 256) 24 8)) 32)))));
      pure ()
    pat_end
