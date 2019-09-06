def vfmsubadd231pd1 : instruction :=
  definst "vfmsubadd231pd" $ do
    pattern fun (v_3123 : reg (bv 128)) (v_3124 : reg (bv 128)) (v_3125 : reg (bv 128)) => do
      v_6656 <- getRegister v_3124;
      v_6659 <- getRegister v_3123;
      v_6663 <- getRegister v_3125;
      setRegister (lhs.of_reg v_3125) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6656 0 64) 53 11) (MInt2Float (extract v_6659 0 64) 53 11)) (MInt2Float (extract v_6663 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6656 64 128) 53 11) (MInt2Float (extract v_6659 64 128) 53 11)) (MInt2Float (extract v_6663 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3137 : reg (bv 256)) (v_3138 : reg (bv 256)) (v_3139 : reg (bv 256)) => do
      v_6684 <- getRegister v_3138;
      v_6687 <- getRegister v_3137;
      v_6691 <- getRegister v_3139;
      setRegister (lhs.of_reg v_3139) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6684 0 64) 53 11) (MInt2Float (extract v_6687 0 64) 53 11)) (MInt2Float (extract v_6691 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6684 64 128) 53 11) (MInt2Float (extract v_6687 64 128) 53 11)) (MInt2Float (extract v_6691 64 128) 53 11)) 64)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6684 128 192) 53 11) (MInt2Float (extract v_6687 128 192) 53 11)) (MInt2Float (extract v_6691 128 192) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6684 192 256) 53 11) (MInt2Float (extract v_6687 192 256) 53 11)) (MInt2Float (extract v_6691 192 256) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_3120 : Mem) (v_3118 : reg (bv 128)) (v_3119 : reg (bv 128)) => do
      v_12454 <- getRegister v_3118;
      v_12457 <- evaluateAddress v_3120;
      v_12458 <- load v_12457 16;
      v_12462 <- getRegister v_3119;
      setRegister (lhs.of_reg v_3119) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12454 0 64) 53 11) (MInt2Float (extract v_12458 0 64) 53 11)) (MInt2Float (extract v_12462 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12454 64 128) 53 11) (MInt2Float (extract v_12458 64 128) 53 11)) (MInt2Float (extract v_12462 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3129 : Mem) (v_3132 : reg (bv 256)) (v_3133 : reg (bv 256)) => do
      v_12478 <- getRegister v_3132;
      v_12481 <- evaluateAddress v_3129;
      v_12482 <- load v_12481 32;
      v_12486 <- getRegister v_3133;
      setRegister (lhs.of_reg v_3133) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12478 0 64) 53 11) (MInt2Float (extract v_12482 0 64) 53 11)) (MInt2Float (extract v_12486 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12478 64 128) 53 11) (MInt2Float (extract v_12482 64 128) 53 11)) (MInt2Float (extract v_12486 64 128) 53 11)) 64)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12478 128 192) 53 11) (MInt2Float (extract v_12482 128 192) 53 11)) (MInt2Float (extract v_12486 128 192) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12478 192 256) 53 11) (MInt2Float (extract v_12482 192 256) 53 11)) (MInt2Float (extract v_12486 192 256) 53 11)) 64)));
      pure ()
    pat_end
