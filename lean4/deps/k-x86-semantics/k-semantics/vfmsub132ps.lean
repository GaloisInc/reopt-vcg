def vfmsub132ps1 : instruction :=
  definst "vfmsub132ps" $ do
    pattern fun (v_2770 : reg (bv 128)) (v_2771 : reg (bv 128)) (v_2772 : reg (bv 128)) => do
      v_5470 <- getRegister v_2772;
      v_5473 <- getRegister v_2770;
      v_5477 <- getRegister v_2771;
      setRegister (lhs.of_reg v_2772) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5470 0 32) 24 8) (MInt2Float (extract v_5473 0 32) 24 8)) (MInt2Float (extract v_5477 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5470 32 64) 24 8) (MInt2Float (extract v_5473 32 64) 24 8)) (MInt2Float (extract v_5477 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5470 64 96) 24 8) (MInt2Float (extract v_5473 64 96) 24 8)) (MInt2Float (extract v_5477 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5470 96 128) 24 8) (MInt2Float (extract v_5473 96 128) 24 8)) (MInt2Float (extract v_5477 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2782 : reg (bv 256)) (v_2783 : reg (bv 256)) (v_2784 : reg (bv 256)) => do
      v_5518 <- getRegister v_2784;
      v_5521 <- getRegister v_2782;
      v_5525 <- getRegister v_2783;
      setRegister (lhs.of_reg v_2784) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5518 0 32) 24 8) (MInt2Float (extract v_5521 0 32) 24 8)) (MInt2Float (extract v_5525 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5518 32 64) 24 8) (MInt2Float (extract v_5521 32 64) 24 8)) (MInt2Float (extract v_5525 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5518 64 96) 24 8) (MInt2Float (extract v_5521 64 96) 24 8)) (MInt2Float (extract v_5525 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5518 96 128) 24 8) (MInt2Float (extract v_5521 96 128) 24 8)) (MInt2Float (extract v_5525 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5518 128 160) 24 8) (MInt2Float (extract v_5521 128 160) 24 8)) (MInt2Float (extract v_5525 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5518 160 192) 24 8) (MInt2Float (extract v_5521 160 192) 24 8)) (MInt2Float (extract v_5525 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5518 192 224) 24 8) (MInt2Float (extract v_5521 192 224) 24 8)) (MInt2Float (extract v_5525 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5518 224 256) 24 8) (MInt2Float (extract v_5521 224 256) 24 8)) (MInt2Float (extract v_5525 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2767 : Mem) (v_2765 : reg (bv 128)) (v_2766 : reg (bv 128)) => do
      v_11353 <- getRegister v_2766;
      v_11356 <- evaluateAddress v_2767;
      v_11357 <- load v_11356 16;
      v_11361 <- getRegister v_2765;
      setRegister (lhs.of_reg v_2766) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11353 0 32) 24 8) (MInt2Float (extract v_11357 0 32) 24 8)) (MInt2Float (extract v_11361 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11353 32 64) 24 8) (MInt2Float (extract v_11357 32 64) 24 8)) (MInt2Float (extract v_11361 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11353 64 96) 24 8) (MInt2Float (extract v_11357 64 96) 24 8)) (MInt2Float (extract v_11361 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11353 96 128) 24 8) (MInt2Float (extract v_11357 96 128) 24 8)) (MInt2Float (extract v_11361 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2776 : Mem) (v_2777 : reg (bv 256)) (v_2778 : reg (bv 256)) => do
      v_11397 <- getRegister v_2778;
      v_11400 <- evaluateAddress v_2776;
      v_11401 <- load v_11400 32;
      v_11405 <- getRegister v_2777;
      setRegister (lhs.of_reg v_2778) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11397 0 32) 24 8) (MInt2Float (extract v_11401 0 32) 24 8)) (MInt2Float (extract v_11405 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11397 32 64) 24 8) (MInt2Float (extract v_11401 32 64) 24 8)) (MInt2Float (extract v_11405 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11397 64 96) 24 8) (MInt2Float (extract v_11401 64 96) 24 8)) (MInt2Float (extract v_11405 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11397 96 128) 24 8) (MInt2Float (extract v_11401 96 128) 24 8)) (MInt2Float (extract v_11405 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11397 128 160) 24 8) (MInt2Float (extract v_11401 128 160) 24 8)) (MInt2Float (extract v_11405 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11397 160 192) 24 8) (MInt2Float (extract v_11401 160 192) 24 8)) (MInt2Float (extract v_11405 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11397 192 224) 24 8) (MInt2Float (extract v_11401 192 224) 24 8)) (MInt2Float (extract v_11405 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11397 224 256) 24 8) (MInt2Float (extract v_11401 224 256) 24 8)) (MInt2Float (extract v_11405 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
