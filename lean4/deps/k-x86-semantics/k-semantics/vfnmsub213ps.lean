def vfnmsub213ps1 : instruction :=
  definst "vfnmsub213ps" $ do
    pattern fun (v_3364 : reg (bv 128)) (v_3365 : reg (bv 128)) (v_3366 : reg (bv 128)) => do
      v_7595 <- getRegister v_3365;
      v_7598 <- getRegister v_3366;
      v_7603 <- getRegister v_3364;
      setRegister (lhs.of_reg v_3366) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7595 0 32) 24 8) (MInt2Float (extract v_7598 0 32) 24 8))) (MInt2Float (extract v_7603 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7595 32 64) 24 8) (MInt2Float (extract v_7598 32 64) 24 8))) (MInt2Float (extract v_7603 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7595 64 96) 24 8) (MInt2Float (extract v_7598 64 96) 24 8))) (MInt2Float (extract v_7603 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7595 96 128) 24 8) (MInt2Float (extract v_7598 96 128) 24 8))) (MInt2Float (extract v_7603 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3376 : reg (bv 256)) (v_3377 : reg (bv 256)) (v_3378 : reg (bv 256)) => do
      v_7647 <- getRegister v_3377;
      v_7650 <- getRegister v_3378;
      v_7655 <- getRegister v_3376;
      setRegister (lhs.of_reg v_3378) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7647 0 32) 24 8) (MInt2Float (extract v_7650 0 32) 24 8))) (MInt2Float (extract v_7655 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7647 32 64) 24 8) (MInt2Float (extract v_7650 32 64) 24 8))) (MInt2Float (extract v_7655 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7647 64 96) 24 8) (MInt2Float (extract v_7650 64 96) 24 8))) (MInt2Float (extract v_7655 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7647 96 128) 24 8) (MInt2Float (extract v_7650 96 128) 24 8))) (MInt2Float (extract v_7655 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7647 128 160) 24 8) (MInt2Float (extract v_7650 128 160) 24 8))) (MInt2Float (extract v_7655 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7647 160 192) 24 8) (MInt2Float (extract v_7650 160 192) 24 8))) (MInt2Float (extract v_7655 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7647 192 224) 24 8) (MInt2Float (extract v_7650 192 224) 24 8))) (MInt2Float (extract v_7655 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7647 224 256) 24 8) (MInt2Float (extract v_7650 224 256) 24 8))) (MInt2Float (extract v_7655 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3361 : Mem) (v_3359 : reg (bv 128)) (v_3360 : reg (bv 128)) => do
      v_13248 <- getRegister v_3359;
      v_13251 <- getRegister v_3360;
      v_13256 <- evaluateAddress v_3361;
      v_13257 <- load v_13256 16;
      setRegister (lhs.of_reg v_3360) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13248 0 32) 24 8) (MInt2Float (extract v_13251 0 32) 24 8))) (MInt2Float (extract v_13257 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13248 32 64) 24 8) (MInt2Float (extract v_13251 32 64) 24 8))) (MInt2Float (extract v_13257 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13248 64 96) 24 8) (MInt2Float (extract v_13251 64 96) 24 8))) (MInt2Float (extract v_13257 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13248 96 128) 24 8) (MInt2Float (extract v_13251 96 128) 24 8))) (MInt2Float (extract v_13257 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3370 : Mem) (v_3371 : reg (bv 256)) (v_3372 : reg (bv 256)) => do
      v_13296 <- getRegister v_3371;
      v_13299 <- getRegister v_3372;
      v_13304 <- evaluateAddress v_3370;
      v_13305 <- load v_13304 32;
      setRegister (lhs.of_reg v_3372) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13296 0 32) 24 8) (MInt2Float (extract v_13299 0 32) 24 8))) (MInt2Float (extract v_13305 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13296 32 64) 24 8) (MInt2Float (extract v_13299 32 64) 24 8))) (MInt2Float (extract v_13305 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13296 64 96) 24 8) (MInt2Float (extract v_13299 64 96) 24 8))) (MInt2Float (extract v_13305 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13296 96 128) 24 8) (MInt2Float (extract v_13299 96 128) 24 8))) (MInt2Float (extract v_13305 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13296 128 160) 24 8) (MInt2Float (extract v_13299 128 160) 24 8))) (MInt2Float (extract v_13305 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13296 160 192) 24 8) (MInt2Float (extract v_13299 160 192) 24 8))) (MInt2Float (extract v_13305 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13296 192 224) 24 8) (MInt2Float (extract v_13299 192 224) 24 8))) (MInt2Float (extract v_13305 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13296 224 256) 24 8) (MInt2Float (extract v_13299 224 256) 24 8))) (MInt2Float (extract v_13305 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
