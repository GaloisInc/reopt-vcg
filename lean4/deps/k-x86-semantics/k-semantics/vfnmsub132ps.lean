def vfnmsub132ps1 : instruction :=
  definst "vfnmsub132ps" $ do
    pattern fun (v_3298 : reg (bv 128)) (v_3299 : reg (bv 128)) (v_3300 : reg (bv 128)) => do
      v_7323 <- getRegister v_3300;
      v_7326 <- getRegister v_3298;
      v_7331 <- getRegister v_3299;
      setRegister (lhs.of_reg v_3300) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7323 0 32) 24 8) (MInt2Float (extract v_7326 0 32) 24 8))) (MInt2Float (extract v_7331 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7323 32 64) 24 8) (MInt2Float (extract v_7326 32 64) 24 8))) (MInt2Float (extract v_7331 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7323 64 96) 24 8) (MInt2Float (extract v_7326 64 96) 24 8))) (MInt2Float (extract v_7331 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7323 96 128) 24 8) (MInt2Float (extract v_7326 96 128) 24 8))) (MInt2Float (extract v_7331 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3310 : reg (bv 256)) (v_3311 : reg (bv 256)) (v_3312 : reg (bv 256)) => do
      v_7375 <- getRegister v_3312;
      v_7378 <- getRegister v_3310;
      v_7383 <- getRegister v_3311;
      setRegister (lhs.of_reg v_3312) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7375 0 32) 24 8) (MInt2Float (extract v_7378 0 32) 24 8))) (MInt2Float (extract v_7383 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7375 32 64) 24 8) (MInt2Float (extract v_7378 32 64) 24 8))) (MInt2Float (extract v_7383 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7375 64 96) 24 8) (MInt2Float (extract v_7378 64 96) 24 8))) (MInt2Float (extract v_7383 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7375 96 128) 24 8) (MInt2Float (extract v_7378 96 128) 24 8))) (MInt2Float (extract v_7383 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7375 128 160) 24 8) (MInt2Float (extract v_7378 128 160) 24 8))) (MInt2Float (extract v_7383 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7375 160 192) 24 8) (MInt2Float (extract v_7378 160 192) 24 8))) (MInt2Float (extract v_7383 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7375 192 224) 24 8) (MInt2Float (extract v_7378 192 224) 24 8))) (MInt2Float (extract v_7383 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7375 224 256) 24 8) (MInt2Float (extract v_7378 224 256) 24 8))) (MInt2Float (extract v_7383 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3295 : Mem) (v_3293 : reg (bv 128)) (v_3294 : reg (bv 128)) => do
      v_13002 <- getRegister v_3294;
      v_13005 <- evaluateAddress v_3295;
      v_13006 <- load v_13005 16;
      v_13011 <- getRegister v_3293;
      setRegister (lhs.of_reg v_3294) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13002 0 32) 24 8) (MInt2Float (extract v_13006 0 32) 24 8))) (MInt2Float (extract v_13011 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13002 32 64) 24 8) (MInt2Float (extract v_13006 32 64) 24 8))) (MInt2Float (extract v_13011 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13002 64 96) 24 8) (MInt2Float (extract v_13006 64 96) 24 8))) (MInt2Float (extract v_13011 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13002 96 128) 24 8) (MInt2Float (extract v_13006 96 128) 24 8))) (MInt2Float (extract v_13011 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3304 : Mem) (v_3305 : reg (bv 256)) (v_3306 : reg (bv 256)) => do
      v_13050 <- getRegister v_3306;
      v_13053 <- evaluateAddress v_3304;
      v_13054 <- load v_13053 32;
      v_13059 <- getRegister v_3305;
      setRegister (lhs.of_reg v_3306) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13050 0 32) 24 8) (MInt2Float (extract v_13054 0 32) 24 8))) (MInt2Float (extract v_13059 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13050 32 64) 24 8) (MInt2Float (extract v_13054 32 64) 24 8))) (MInt2Float (extract v_13059 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13050 64 96) 24 8) (MInt2Float (extract v_13054 64 96) 24 8))) (MInt2Float (extract v_13059 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13050 96 128) 24 8) (MInt2Float (extract v_13054 96 128) 24 8))) (MInt2Float (extract v_13059 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13050 128 160) 24 8) (MInt2Float (extract v_13054 128 160) 24 8))) (MInt2Float (extract v_13059 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13050 160 192) 24 8) (MInt2Float (extract v_13054 160 192) 24 8))) (MInt2Float (extract v_13059 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13050 192 224) 24 8) (MInt2Float (extract v_13054 192 224) 24 8))) (MInt2Float (extract v_13059 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13050 224 256) 24 8) (MInt2Float (extract v_13054 224 256) 24 8))) (MInt2Float (extract v_13059 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
