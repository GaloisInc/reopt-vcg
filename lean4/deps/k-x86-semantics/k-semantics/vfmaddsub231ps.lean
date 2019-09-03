def vfmaddsub231ps1 : instruction :=
  definst "vfmaddsub231ps" $ do
    pattern fun (v_2726 : reg (bv 128)) (v_2727 : reg (bv 128)) (v_2728 : reg (bv 128)) => do
      v_5258 <- getRegister v_2727;
      v_5261 <- getRegister v_2726;
      v_5265 <- getRegister v_2728;
      setRegister (lhs.of_reg v_2728) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5258 0 32) 24 8) (MInt2Float (extract v_5261 0 32) 24 8)) (MInt2Float (extract v_5265 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5258 32 64) 24 8) (MInt2Float (extract v_5261 32 64) 24 8)) (MInt2Float (extract v_5265 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5258 64 96) 24 8) (MInt2Float (extract v_5261 64 96) 24 8)) (MInt2Float (extract v_5265 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5258 96 128) 24 8) (MInt2Float (extract v_5261 96 128) 24 8)) (MInt2Float (extract v_5265 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2738 : reg (bv 256)) (v_2739 : reg (bv 256)) (v_2740 : reg (bv 256)) => do
      v_5306 <- getRegister v_2739;
      v_5309 <- getRegister v_2738;
      v_5313 <- getRegister v_2740;
      setRegister (lhs.of_reg v_2740) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5306 0 32) 24 8) (MInt2Float (extract v_5309 0 32) 24 8)) (MInt2Float (extract v_5313 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5306 32 64) 24 8) (MInt2Float (extract v_5309 32 64) 24 8)) (MInt2Float (extract v_5313 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5306 64 96) 24 8) (MInt2Float (extract v_5309 64 96) 24 8)) (MInt2Float (extract v_5313 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5306 96 128) 24 8) (MInt2Float (extract v_5309 96 128) 24 8)) (MInt2Float (extract v_5313 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5306 128 160) 24 8) (MInt2Float (extract v_5309 128 160) 24 8)) (MInt2Float (extract v_5313 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5306 160 192) 24 8) (MInt2Float (extract v_5309 160 192) 24 8)) (MInt2Float (extract v_5313 160 192) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5306 192 224) 24 8) (MInt2Float (extract v_5309 192 224) 24 8)) (MInt2Float (extract v_5313 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5306 224 256) 24 8) (MInt2Float (extract v_5309 224 256) 24 8)) (MInt2Float (extract v_5313 224 256) 24 8)) 32)))));
      pure ()
    pat_end;
    pattern fun (v_2723 : Mem) (v_2721 : reg (bv 128)) (v_2722 : reg (bv 128)) => do
      v_11157 <- getRegister v_2721;
      v_11160 <- evaluateAddress v_2723;
      v_11161 <- load v_11160 16;
      v_11165 <- getRegister v_2722;
      setRegister (lhs.of_reg v_2722) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11157 0 32) 24 8) (MInt2Float (extract v_11161 0 32) 24 8)) (MInt2Float (extract v_11165 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11157 32 64) 24 8) (MInt2Float (extract v_11161 32 64) 24 8)) (MInt2Float (extract v_11165 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11157 64 96) 24 8) (MInt2Float (extract v_11161 64 96) 24 8)) (MInt2Float (extract v_11165 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11157 96 128) 24 8) (MInt2Float (extract v_11161 96 128) 24 8)) (MInt2Float (extract v_11165 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2732 : Mem) (v_2733 : reg (bv 256)) (v_2734 : reg (bv 256)) => do
      v_11201 <- getRegister v_2733;
      v_11204 <- evaluateAddress v_2732;
      v_11205 <- load v_11204 32;
      v_11209 <- getRegister v_2734;
      setRegister (lhs.of_reg v_2734) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11201 0 32) 24 8) (MInt2Float (extract v_11205 0 32) 24 8)) (MInt2Float (extract v_11209 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11201 32 64) 24 8) (MInt2Float (extract v_11205 32 64) 24 8)) (MInt2Float (extract v_11209 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11201 64 96) 24 8) (MInt2Float (extract v_11205 64 96) 24 8)) (MInt2Float (extract v_11209 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11201 96 128) 24 8) (MInt2Float (extract v_11205 96 128) 24 8)) (MInt2Float (extract v_11209 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11201 128 160) 24 8) (MInt2Float (extract v_11205 128 160) 24 8)) (MInt2Float (extract v_11209 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11201 160 192) 24 8) (MInt2Float (extract v_11205 160 192) 24 8)) (MInt2Float (extract v_11209 160 192) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11201 192 224) 24 8) (MInt2Float (extract v_11205 192 224) 24 8)) (MInt2Float (extract v_11209 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11201 224 256) 24 8) (MInt2Float (extract v_11205 224 256) 24 8)) (MInt2Float (extract v_11209 224 256) 24 8)) 32)))));
      pure ()
    pat_end
