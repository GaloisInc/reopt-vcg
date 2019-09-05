def vfmsub132ps1 : instruction :=
  definst "vfmsub132ps" $ do
    pattern fun (v_2835 : reg (bv 128)) (v_2836 : reg (bv 128)) (v_2837 : reg (bv 128)) => do
      v_5537 <- getRegister v_2837;
      v_5540 <- getRegister v_2835;
      v_5544 <- getRegister v_2836;
      setRegister (lhs.of_reg v_2837) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5537 0 32) 24 8) (MInt2Float (extract v_5540 0 32) 24 8)) (MInt2Float (extract v_5544 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5537 32 64) 24 8) (MInt2Float (extract v_5540 32 64) 24 8)) (MInt2Float (extract v_5544 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5537 64 96) 24 8) (MInt2Float (extract v_5540 64 96) 24 8)) (MInt2Float (extract v_5544 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5537 96 128) 24 8) (MInt2Float (extract v_5540 96 128) 24 8)) (MInt2Float (extract v_5544 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2845 : reg (bv 256)) (v_2846 : reg (bv 256)) (v_2847 : reg (bv 256)) => do
      v_5585 <- getRegister v_2847;
      v_5588 <- getRegister v_2845;
      v_5592 <- getRegister v_2846;
      setRegister (lhs.of_reg v_2847) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5585 0 32) 24 8) (MInt2Float (extract v_5588 0 32) 24 8)) (MInt2Float (extract v_5592 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5585 32 64) 24 8) (MInt2Float (extract v_5588 32 64) 24 8)) (MInt2Float (extract v_5592 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5585 64 96) 24 8) (MInt2Float (extract v_5588 64 96) 24 8)) (MInt2Float (extract v_5592 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5585 96 128) 24 8) (MInt2Float (extract v_5588 96 128) 24 8)) (MInt2Float (extract v_5592 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5585 128 160) 24 8) (MInt2Float (extract v_5588 128 160) 24 8)) (MInt2Float (extract v_5592 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5585 160 192) 24 8) (MInt2Float (extract v_5588 160 192) 24 8)) (MInt2Float (extract v_5592 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5585 192 224) 24 8) (MInt2Float (extract v_5588 192 224) 24 8)) (MInt2Float (extract v_5592 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5585 224 256) 24 8) (MInt2Float (extract v_5588 224 256) 24 8)) (MInt2Float (extract v_5592 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2829 : Mem) (v_2830 : reg (bv 128)) (v_2831 : reg (bv 128)) => do
      v_11437 <- getRegister v_2831;
      v_11440 <- evaluateAddress v_2829;
      v_11441 <- load v_11440 16;
      v_11445 <- getRegister v_2830;
      setRegister (lhs.of_reg v_2831) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11437 0 32) 24 8) (MInt2Float (extract v_11441 0 32) 24 8)) (MInt2Float (extract v_11445 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11437 32 64) 24 8) (MInt2Float (extract v_11441 32 64) 24 8)) (MInt2Float (extract v_11445 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11437 64 96) 24 8) (MInt2Float (extract v_11441 64 96) 24 8)) (MInt2Float (extract v_11445 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11437 96 128) 24 8) (MInt2Float (extract v_11441 96 128) 24 8)) (MInt2Float (extract v_11445 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2840 : Mem) (v_2841 : reg (bv 256)) (v_2842 : reg (bv 256)) => do
      v_11481 <- getRegister v_2842;
      v_11484 <- evaluateAddress v_2840;
      v_11485 <- load v_11484 32;
      v_11489 <- getRegister v_2841;
      setRegister (lhs.of_reg v_2842) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11481 0 32) 24 8) (MInt2Float (extract v_11485 0 32) 24 8)) (MInt2Float (extract v_11489 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11481 32 64) 24 8) (MInt2Float (extract v_11485 32 64) 24 8)) (MInt2Float (extract v_11489 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11481 64 96) 24 8) (MInt2Float (extract v_11485 64 96) 24 8)) (MInt2Float (extract v_11489 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11481 96 128) 24 8) (MInt2Float (extract v_11485 96 128) 24 8)) (MInt2Float (extract v_11489 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11481 128 160) 24 8) (MInt2Float (extract v_11485 128 160) 24 8)) (MInt2Float (extract v_11489 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11481 160 192) 24 8) (MInt2Float (extract v_11485 160 192) 24 8)) (MInt2Float (extract v_11489 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11481 192 224) 24 8) (MInt2Float (extract v_11485 192 224) 24 8)) (MInt2Float (extract v_11489 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11481 224 256) 24 8) (MInt2Float (extract v_11485 224 256) 24 8)) (MInt2Float (extract v_11489 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
