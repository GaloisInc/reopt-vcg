def vfmaddsub231ps1 : instruction :=
  definst "vfmaddsub231ps" $ do
    pattern fun (v_2791 : reg (bv 128)) (v_2792 : reg (bv 128)) (v_2793 : reg (bv 128)) => do
      v_5325 <- getRegister v_2792;
      v_5328 <- getRegister v_2791;
      v_5332 <- getRegister v_2793;
      setRegister (lhs.of_reg v_2793) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5325 0 32) 24 8) (MInt2Float (extract v_5328 0 32) 24 8)) (MInt2Float (extract v_5332 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5325 32 64) 24 8) (MInt2Float (extract v_5328 32 64) 24 8)) (MInt2Float (extract v_5332 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5325 64 96) 24 8) (MInt2Float (extract v_5328 64 96) 24 8)) (MInt2Float (extract v_5332 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5325 96 128) 24 8) (MInt2Float (extract v_5328 96 128) 24 8)) (MInt2Float (extract v_5332 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2801 : reg (bv 256)) (v_2802 : reg (bv 256)) (v_2803 : reg (bv 256)) => do
      v_5373 <- getRegister v_2802;
      v_5376 <- getRegister v_2801;
      v_5380 <- getRegister v_2803;
      setRegister (lhs.of_reg v_2803) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5373 0 32) 24 8) (MInt2Float (extract v_5376 0 32) 24 8)) (MInt2Float (extract v_5380 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5373 32 64) 24 8) (MInt2Float (extract v_5376 32 64) 24 8)) (MInt2Float (extract v_5380 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5373 64 96) 24 8) (MInt2Float (extract v_5376 64 96) 24 8)) (MInt2Float (extract v_5380 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5373 96 128) 24 8) (MInt2Float (extract v_5376 96 128) 24 8)) (MInt2Float (extract v_5380 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5373 128 160) 24 8) (MInt2Float (extract v_5376 128 160) 24 8)) (MInt2Float (extract v_5380 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5373 160 192) 24 8) (MInt2Float (extract v_5376 160 192) 24 8)) (MInt2Float (extract v_5380 160 192) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5373 192 224) 24 8) (MInt2Float (extract v_5376 192 224) 24 8)) (MInt2Float (extract v_5380 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5373 224 256) 24 8) (MInt2Float (extract v_5376 224 256) 24 8)) (MInt2Float (extract v_5380 224 256) 24 8)) 32)))));
      pure ()
    pat_end;
    pattern fun (v_2785 : Mem) (v_2786 : reg (bv 128)) (v_2787 : reg (bv 128)) => do
      v_11241 <- getRegister v_2786;
      v_11244 <- evaluateAddress v_2785;
      v_11245 <- load v_11244 16;
      v_11249 <- getRegister v_2787;
      setRegister (lhs.of_reg v_2787) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11241 0 32) 24 8) (MInt2Float (extract v_11245 0 32) 24 8)) (MInt2Float (extract v_11249 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11241 32 64) 24 8) (MInt2Float (extract v_11245 32 64) 24 8)) (MInt2Float (extract v_11249 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11241 64 96) 24 8) (MInt2Float (extract v_11245 64 96) 24 8)) (MInt2Float (extract v_11249 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11241 96 128) 24 8) (MInt2Float (extract v_11245 96 128) 24 8)) (MInt2Float (extract v_11249 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2796 : Mem) (v_2797 : reg (bv 256)) (v_2798 : reg (bv 256)) => do
      v_11285 <- getRegister v_2797;
      v_11288 <- evaluateAddress v_2796;
      v_11289 <- load v_11288 32;
      v_11293 <- getRegister v_2798;
      setRegister (lhs.of_reg v_2798) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11285 0 32) 24 8) (MInt2Float (extract v_11289 0 32) 24 8)) (MInt2Float (extract v_11293 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11285 32 64) 24 8) (MInt2Float (extract v_11289 32 64) 24 8)) (MInt2Float (extract v_11293 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11285 64 96) 24 8) (MInt2Float (extract v_11289 64 96) 24 8)) (MInt2Float (extract v_11293 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11285 96 128) 24 8) (MInt2Float (extract v_11289 96 128) 24 8)) (MInt2Float (extract v_11293 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11285 128 160) 24 8) (MInt2Float (extract v_11289 128 160) 24 8)) (MInt2Float (extract v_11293 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11285 160 192) 24 8) (MInt2Float (extract v_11289 160 192) 24 8)) (MInt2Float (extract v_11293 160 192) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11285 192 224) 24 8) (MInt2Float (extract v_11289 192 224) 24 8)) (MInt2Float (extract v_11293 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11285 224 256) 24 8) (MInt2Float (extract v_11289 224 256) 24 8)) (MInt2Float (extract v_11293 224 256) 24 8)) 32)))));
      pure ()
    pat_end
