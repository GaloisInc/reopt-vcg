def vfnmsub132ps1 : instruction :=
  definst "vfnmsub132ps" $ do
    pattern fun (v_3387 : reg (bv 128)) (v_3388 : reg (bv 128)) (v_3389 : reg (bv 128)) => do
      v_7427 <- getRegister v_3389;
      v_7430 <- getRegister v_3387;
      v_7435 <- getRegister v_3388;
      setRegister (lhs.of_reg v_3389) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7427 0 32) 24 8) (MInt2Float (extract v_7430 0 32) 24 8))) (MInt2Float (extract v_7435 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7427 32 64) 24 8) (MInt2Float (extract v_7430 32 64) 24 8))) (MInt2Float (extract v_7435 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7427 64 96) 24 8) (MInt2Float (extract v_7430 64 96) 24 8))) (MInt2Float (extract v_7435 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7427 96 128) 24 8) (MInt2Float (extract v_7430 96 128) 24 8))) (MInt2Float (extract v_7435 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3401 : reg (bv 256)) (v_3402 : reg (bv 256)) (v_3403 : reg (bv 256)) => do
      v_7479 <- getRegister v_3403;
      v_7482 <- getRegister v_3401;
      v_7487 <- getRegister v_3402;
      setRegister (lhs.of_reg v_3403) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7479 0 32) 24 8) (MInt2Float (extract v_7482 0 32) 24 8))) (MInt2Float (extract v_7487 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7479 32 64) 24 8) (MInt2Float (extract v_7482 32 64) 24 8))) (MInt2Float (extract v_7487 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7479 64 96) 24 8) (MInt2Float (extract v_7482 64 96) 24 8))) (MInt2Float (extract v_7487 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7479 96 128) 24 8) (MInt2Float (extract v_7482 96 128) 24 8))) (MInt2Float (extract v_7487 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7479 128 160) 24 8) (MInt2Float (extract v_7482 128 160) 24 8))) (MInt2Float (extract v_7487 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7479 160 192) 24 8) (MInt2Float (extract v_7482 160 192) 24 8))) (MInt2Float (extract v_7487 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7479 192 224) 24 8) (MInt2Float (extract v_7482 192 224) 24 8))) (MInt2Float (extract v_7487 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7479 224 256) 24 8) (MInt2Float (extract v_7482 224 256) 24 8))) (MInt2Float (extract v_7487 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3384 : Mem) (v_3382 : reg (bv 128)) (v_3383 : reg (bv 128)) => do
      v_13123 <- getRegister v_3383;
      v_13126 <- evaluateAddress v_3384;
      v_13127 <- load v_13126 16;
      v_13132 <- getRegister v_3382;
      setRegister (lhs.of_reg v_3383) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13123 0 32) 24 8) (MInt2Float (extract v_13127 0 32) 24 8))) (MInt2Float (extract v_13132 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13123 32 64) 24 8) (MInt2Float (extract v_13127 32 64) 24 8))) (MInt2Float (extract v_13132 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13123 64 96) 24 8) (MInt2Float (extract v_13127 64 96) 24 8))) (MInt2Float (extract v_13132 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13123 96 128) 24 8) (MInt2Float (extract v_13127 96 128) 24 8))) (MInt2Float (extract v_13132 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3393 : Mem) (v_3396 : reg (bv 256)) (v_3397 : reg (bv 256)) => do
      v_13171 <- getRegister v_3397;
      v_13174 <- evaluateAddress v_3393;
      v_13175 <- load v_13174 32;
      v_13180 <- getRegister v_3396;
      setRegister (lhs.of_reg v_3397) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13171 0 32) 24 8) (MInt2Float (extract v_13175 0 32) 24 8))) (MInt2Float (extract v_13180 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13171 32 64) 24 8) (MInt2Float (extract v_13175 32 64) 24 8))) (MInt2Float (extract v_13180 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13171 64 96) 24 8) (MInt2Float (extract v_13175 64 96) 24 8))) (MInt2Float (extract v_13180 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13171 96 128) 24 8) (MInt2Float (extract v_13175 96 128) 24 8))) (MInt2Float (extract v_13180 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13171 128 160) 24 8) (MInt2Float (extract v_13175 128 160) 24 8))) (MInt2Float (extract v_13180 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13171 160 192) 24 8) (MInt2Float (extract v_13175 160 192) 24 8))) (MInt2Float (extract v_13180 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13171 192 224) 24 8) (MInt2Float (extract v_13175 192 224) 24 8))) (MInt2Float (extract v_13180 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13171 224 256) 24 8) (MInt2Float (extract v_13175 224 256) 24 8))) (MInt2Float (extract v_13180 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
