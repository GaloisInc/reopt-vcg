def vfmadd132ps1 : instruction :=
  definst "vfmadd132ps" $ do
    pattern fun (v_2440 : reg (bv 128)) (v_2441 : reg (bv 128)) (v_2442 : reg (bv 128)) => do
      v_4103 <- getRegister v_2442;
      v_4106 <- getRegister v_2440;
      v_4110 <- getRegister v_2441;
      setRegister (lhs.of_reg v_2442) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4103 0 32) 24 8) (MInt2Float (extract v_4106 0 32) 24 8)) (MInt2Float (extract v_4110 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4103 32 64) 24 8) (MInt2Float (extract v_4106 32 64) 24 8)) (MInt2Float (extract v_4110 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4103 64 96) 24 8) (MInt2Float (extract v_4106 64 96) 24 8)) (MInt2Float (extract v_4110 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4103 96 128) 24 8) (MInt2Float (extract v_4106 96 128) 24 8)) (MInt2Float (extract v_4110 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2452 : reg (bv 256)) (v_2453 : reg (bv 256)) (v_2454 : reg (bv 256)) => do
      v_4151 <- getRegister v_2454;
      v_4154 <- getRegister v_2452;
      v_4158 <- getRegister v_2453;
      setRegister (lhs.of_reg v_2454) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4151 0 32) 24 8) (MInt2Float (extract v_4154 0 32) 24 8)) (MInt2Float (extract v_4158 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4151 32 64) 24 8) (MInt2Float (extract v_4154 32 64) 24 8)) (MInt2Float (extract v_4158 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4151 64 96) 24 8) (MInt2Float (extract v_4154 64 96) 24 8)) (MInt2Float (extract v_4158 64 96) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4151 96 128) 24 8) (MInt2Float (extract v_4154 96 128) 24 8)) (MInt2Float (extract v_4158 96 128) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4151 128 160) 24 8) (MInt2Float (extract v_4154 128 160) 24 8)) (MInt2Float (extract v_4158 128 160) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4151 160 192) 24 8) (MInt2Float (extract v_4154 160 192) 24 8)) (MInt2Float (extract v_4158 160 192) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4151 192 224) 24 8) (MInt2Float (extract v_4154 192 224) 24 8)) (MInt2Float (extract v_4158 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4151 224 256) 24 8) (MInt2Float (extract v_4154 224 256) 24 8)) (MInt2Float (extract v_4158 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2437 : Mem) (v_2435 : reg (bv 128)) (v_2436 : reg (bv 128)) => do
      v_10112 <- getRegister v_2436;
      v_10115 <- evaluateAddress v_2437;
      v_10116 <- load v_10115 16;
      v_10120 <- getRegister v_2435;
      setRegister (lhs.of_reg v_2436) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10112 0 32) 24 8) (MInt2Float (extract v_10116 0 32) 24 8)) (MInt2Float (extract v_10120 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10112 32 64) 24 8) (MInt2Float (extract v_10116 32 64) 24 8)) (MInt2Float (extract v_10120 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10112 64 96) 24 8) (MInt2Float (extract v_10116 64 96) 24 8)) (MInt2Float (extract v_10120 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10112 96 128) 24 8) (MInt2Float (extract v_10116 96 128) 24 8)) (MInt2Float (extract v_10120 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2446 : Mem) (v_2447 : reg (bv 256)) (v_2448 : reg (bv 256)) => do
      v_10156 <- getRegister v_2448;
      v_10159 <- evaluateAddress v_2446;
      v_10160 <- load v_10159 32;
      v_10164 <- getRegister v_2447;
      setRegister (lhs.of_reg v_2448) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10156 0 32) 24 8) (MInt2Float (extract v_10160 0 32) 24 8)) (MInt2Float (extract v_10164 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10156 32 64) 24 8) (MInt2Float (extract v_10160 32 64) 24 8)) (MInt2Float (extract v_10164 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10156 64 96) 24 8) (MInt2Float (extract v_10160 64 96) 24 8)) (MInt2Float (extract v_10164 64 96) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10156 96 128) 24 8) (MInt2Float (extract v_10160 96 128) 24 8)) (MInt2Float (extract v_10164 96 128) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10156 128 160) 24 8) (MInt2Float (extract v_10160 128 160) 24 8)) (MInt2Float (extract v_10164 128 160) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10156 160 192) 24 8) (MInt2Float (extract v_10160 160 192) 24 8)) (MInt2Float (extract v_10164 160 192) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10156 192 224) 24 8) (MInt2Float (extract v_10160 192 224) 24 8)) (MInt2Float (extract v_10164 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10156 224 256) 24 8) (MInt2Float (extract v_10160 224 256) 24 8)) (MInt2Float (extract v_10164 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
