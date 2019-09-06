def vfmaddsub231ps1 : instruction :=
  definst "vfmaddsub231ps" $ do
    pattern fun (v_2815 : reg (bv 128)) (v_2816 : reg (bv 128)) (v_2817 : reg (bv 128)) => do
      v_5352 <- getRegister v_2816;
      v_5355 <- getRegister v_2815;
      v_5359 <- getRegister v_2817;
      setRegister (lhs.of_reg v_2817) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5352 0 32) 24 8) (MInt2Float (extract v_5355 0 32) 24 8)) (MInt2Float (extract v_5359 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5352 32 64) 24 8) (MInt2Float (extract v_5355 32 64) 24 8)) (MInt2Float (extract v_5359 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5352 64 96) 24 8) (MInt2Float (extract v_5355 64 96) 24 8)) (MInt2Float (extract v_5359 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5352 96 128) 24 8) (MInt2Float (extract v_5355 96 128) 24 8)) (MInt2Float (extract v_5359 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2829 : reg (bv 256)) (v_2830 : reg (bv 256)) (v_2831 : reg (bv 256)) => do
      v_5400 <- getRegister v_2830;
      v_5403 <- getRegister v_2829;
      v_5407 <- getRegister v_2831;
      setRegister (lhs.of_reg v_2831) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5400 0 32) 24 8) (MInt2Float (extract v_5403 0 32) 24 8)) (MInt2Float (extract v_5407 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5400 32 64) 24 8) (MInt2Float (extract v_5403 32 64) 24 8)) (MInt2Float (extract v_5407 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5400 64 96) 24 8) (MInt2Float (extract v_5403 64 96) 24 8)) (MInt2Float (extract v_5407 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5400 96 128) 24 8) (MInt2Float (extract v_5403 96 128) 24 8)) (MInt2Float (extract v_5407 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5400 128 160) 24 8) (MInt2Float (extract v_5403 128 160) 24 8)) (MInt2Float (extract v_5407 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5400 160 192) 24 8) (MInt2Float (extract v_5403 160 192) 24 8)) (MInt2Float (extract v_5407 160 192) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5400 192 224) 24 8) (MInt2Float (extract v_5403 192 224) 24 8)) (MInt2Float (extract v_5407 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5400 224 256) 24 8) (MInt2Float (extract v_5403 224 256) 24 8)) (MInt2Float (extract v_5407 224 256) 24 8)) 32)))));
      pure ()
    pat_end;
    pattern fun (v_2812 : Mem) (v_2810 : reg (bv 128)) (v_2811 : reg (bv 128)) => do
      v_11268 <- getRegister v_2810;
      v_11271 <- evaluateAddress v_2812;
      v_11272 <- load v_11271 16;
      v_11276 <- getRegister v_2811;
      setRegister (lhs.of_reg v_2811) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11268 0 32) 24 8) (MInt2Float (extract v_11272 0 32) 24 8)) (MInt2Float (extract v_11276 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11268 32 64) 24 8) (MInt2Float (extract v_11272 32 64) 24 8)) (MInt2Float (extract v_11276 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11268 64 96) 24 8) (MInt2Float (extract v_11272 64 96) 24 8)) (MInt2Float (extract v_11276 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11268 96 128) 24 8) (MInt2Float (extract v_11272 96 128) 24 8)) (MInt2Float (extract v_11276 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2821 : Mem) (v_2824 : reg (bv 256)) (v_2825 : reg (bv 256)) => do
      v_11312 <- getRegister v_2824;
      v_11315 <- evaluateAddress v_2821;
      v_11316 <- load v_11315 32;
      v_11320 <- getRegister v_2825;
      setRegister (lhs.of_reg v_2825) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11312 0 32) 24 8) (MInt2Float (extract v_11316 0 32) 24 8)) (MInt2Float (extract v_11320 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11312 32 64) 24 8) (MInt2Float (extract v_11316 32 64) 24 8)) (MInt2Float (extract v_11320 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11312 64 96) 24 8) (MInt2Float (extract v_11316 64 96) 24 8)) (MInt2Float (extract v_11320 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11312 96 128) 24 8) (MInt2Float (extract v_11316 96 128) 24 8)) (MInt2Float (extract v_11320 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11312 128 160) 24 8) (MInt2Float (extract v_11316 128 160) 24 8)) (MInt2Float (extract v_11320 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11312 160 192) 24 8) (MInt2Float (extract v_11316 160 192) 24 8)) (MInt2Float (extract v_11320 160 192) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11312 192 224) 24 8) (MInt2Float (extract v_11316 192 224) 24 8)) (MInt2Float (extract v_11320 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11312 224 256) 24 8) (MInt2Float (extract v_11316 224 256) 24 8)) (MInt2Float (extract v_11320 224 256) 24 8)) 32)))));
      pure ()
    pat_end
