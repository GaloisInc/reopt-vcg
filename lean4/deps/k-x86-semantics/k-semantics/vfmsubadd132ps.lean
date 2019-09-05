def vfmsubadd132ps1 : instruction :=
  definst "vfmsubadd132ps" $ do
    pattern fun (v_3033 : reg (bv 128)) (v_3034 : reg (bv 128)) (v_3035 : reg (bv 128)) => do
      v_6281 <- getRegister v_3035;
      v_6284 <- getRegister v_3033;
      v_6288 <- getRegister v_3034;
      setRegister (lhs.of_reg v_3035) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6281 0 32) 24 8) (MInt2Float (extract v_6284 0 32) 24 8)) (MInt2Float (extract v_6288 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6281 32 64) 24 8) (MInt2Float (extract v_6284 32 64) 24 8)) (MInt2Float (extract v_6288 32 64) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6281 64 96) 24 8) (MInt2Float (extract v_6284 64 96) 24 8)) (MInt2Float (extract v_6288 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6281 96 128) 24 8) (MInt2Float (extract v_6284 96 128) 24 8)) (MInt2Float (extract v_6288 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_3043 : reg (bv 256)) (v_3044 : reg (bv 256)) (v_3045 : reg (bv 256)) => do
      v_6329 <- getRegister v_3045;
      v_6332 <- getRegister v_3043;
      v_6336 <- getRegister v_3044;
      setRegister (lhs.of_reg v_3045) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6329 0 32) 24 8) (MInt2Float (extract v_6332 0 32) 24 8)) (MInt2Float (extract v_6336 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6329 32 64) 24 8) (MInt2Float (extract v_6332 32 64) 24 8)) (MInt2Float (extract v_6336 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6329 64 96) 24 8) (MInt2Float (extract v_6332 64 96) 24 8)) (MInt2Float (extract v_6336 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6329 96 128) 24 8) (MInt2Float (extract v_6332 96 128) 24 8)) (MInt2Float (extract v_6336 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6329 128 160) 24 8) (MInt2Float (extract v_6332 128 160) 24 8)) (MInt2Float (extract v_6336 128 160) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6329 160 192) 24 8) (MInt2Float (extract v_6332 160 192) 24 8)) (MInt2Float (extract v_6336 160 192) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6329 192 224) 24 8) (MInt2Float (extract v_6332 192 224) 24 8)) (MInt2Float (extract v_6336 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6329 224 256) 24 8) (MInt2Float (extract v_6332 224 256) 24 8)) (MInt2Float (extract v_6336 224 256) 24 8)) 32)))));
      pure ()
    pat_end;
    pattern fun (v_3027 : Mem) (v_3028 : reg (bv 128)) (v_3029 : reg (bv 128)) => do
      v_12103 <- getRegister v_3029;
      v_12106 <- evaluateAddress v_3027;
      v_12107 <- load v_12106 16;
      v_12111 <- getRegister v_3028;
      setRegister (lhs.of_reg v_3029) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12103 0 32) 24 8) (MInt2Float (extract v_12107 0 32) 24 8)) (MInt2Float (extract v_12111 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12103 32 64) 24 8) (MInt2Float (extract v_12107 32 64) 24 8)) (MInt2Float (extract v_12111 32 64) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12103 64 96) 24 8) (MInt2Float (extract v_12107 64 96) 24 8)) (MInt2Float (extract v_12111 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12103 96 128) 24 8) (MInt2Float (extract v_12107 96 128) 24 8)) (MInt2Float (extract v_12111 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_3038 : Mem) (v_3039 : reg (bv 256)) (v_3040 : reg (bv 256)) => do
      v_12147 <- getRegister v_3040;
      v_12150 <- evaluateAddress v_3038;
      v_12151 <- load v_12150 32;
      v_12155 <- getRegister v_3039;
      setRegister (lhs.of_reg v_3040) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12147 0 32) 24 8) (MInt2Float (extract v_12151 0 32) 24 8)) (MInt2Float (extract v_12155 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12147 32 64) 24 8) (MInt2Float (extract v_12151 32 64) 24 8)) (MInt2Float (extract v_12155 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12147 64 96) 24 8) (MInt2Float (extract v_12151 64 96) 24 8)) (MInt2Float (extract v_12155 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12147 96 128) 24 8) (MInt2Float (extract v_12151 96 128) 24 8)) (MInt2Float (extract v_12155 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12147 128 160) 24 8) (MInt2Float (extract v_12151 128 160) 24 8)) (MInt2Float (extract v_12155 128 160) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12147 160 192) 24 8) (MInt2Float (extract v_12151 160 192) 24 8)) (MInt2Float (extract v_12155 160 192) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12147 192 224) 24 8) (MInt2Float (extract v_12151 192 224) 24 8)) (MInt2Float (extract v_12155 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12147 224 256) 24 8) (MInt2Float (extract v_12151 224 256) 24 8)) (MInt2Float (extract v_12155 224 256) 24 8)) 32)))));
      pure ()
    pat_end
