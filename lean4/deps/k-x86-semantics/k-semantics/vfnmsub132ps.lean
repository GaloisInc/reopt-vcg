def vfnmsub132ps1 : instruction :=
  definst "vfnmsub132ps" $ do
    pattern fun (v_3363 : reg (bv 128)) (v_3364 : reg (bv 128)) (v_3365 : reg (bv 128)) => do
      v_7400 <- getRegister v_3365;
      v_7403 <- getRegister v_3363;
      v_7408 <- getRegister v_3364;
      setRegister (lhs.of_reg v_3365) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7400 0 32) 24 8) (MInt2Float (extract v_7403 0 32) 24 8))) (MInt2Float (extract v_7408 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7400 32 64) 24 8) (MInt2Float (extract v_7403 32 64) 24 8))) (MInt2Float (extract v_7408 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7400 64 96) 24 8) (MInt2Float (extract v_7403 64 96) 24 8))) (MInt2Float (extract v_7408 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7400 96 128) 24 8) (MInt2Float (extract v_7403 96 128) 24 8))) (MInt2Float (extract v_7408 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3373 : reg (bv 256)) (v_3374 : reg (bv 256)) (v_3375 : reg (bv 256)) => do
      v_7452 <- getRegister v_3375;
      v_7455 <- getRegister v_3373;
      v_7460 <- getRegister v_3374;
      setRegister (lhs.of_reg v_3375) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7452 0 32) 24 8) (MInt2Float (extract v_7455 0 32) 24 8))) (MInt2Float (extract v_7460 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7452 32 64) 24 8) (MInt2Float (extract v_7455 32 64) 24 8))) (MInt2Float (extract v_7460 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7452 64 96) 24 8) (MInt2Float (extract v_7455 64 96) 24 8))) (MInt2Float (extract v_7460 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7452 96 128) 24 8) (MInt2Float (extract v_7455 96 128) 24 8))) (MInt2Float (extract v_7460 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7452 128 160) 24 8) (MInt2Float (extract v_7455 128 160) 24 8))) (MInt2Float (extract v_7460 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7452 160 192) 24 8) (MInt2Float (extract v_7455 160 192) 24 8))) (MInt2Float (extract v_7460 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7452 192 224) 24 8) (MInt2Float (extract v_7455 192 224) 24 8))) (MInt2Float (extract v_7460 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7452 224 256) 24 8) (MInt2Float (extract v_7455 224 256) 24 8))) (MInt2Float (extract v_7460 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3357 : Mem) (v_3358 : reg (bv 128)) (v_3359 : reg (bv 128)) => do
      v_13096 <- getRegister v_3359;
      v_13099 <- evaluateAddress v_3357;
      v_13100 <- load v_13099 16;
      v_13105 <- getRegister v_3358;
      setRegister (lhs.of_reg v_3359) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13096 0 32) 24 8) (MInt2Float (extract v_13100 0 32) 24 8))) (MInt2Float (extract v_13105 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13096 32 64) 24 8) (MInt2Float (extract v_13100 32 64) 24 8))) (MInt2Float (extract v_13105 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13096 64 96) 24 8) (MInt2Float (extract v_13100 64 96) 24 8))) (MInt2Float (extract v_13105 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13096 96 128) 24 8) (MInt2Float (extract v_13100 96 128) 24 8))) (MInt2Float (extract v_13105 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3368 : Mem) (v_3369 : reg (bv 256)) (v_3370 : reg (bv 256)) => do
      v_13144 <- getRegister v_3370;
      v_13147 <- evaluateAddress v_3368;
      v_13148 <- load v_13147 32;
      v_13153 <- getRegister v_3369;
      setRegister (lhs.of_reg v_3370) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13144 0 32) 24 8) (MInt2Float (extract v_13148 0 32) 24 8))) (MInt2Float (extract v_13153 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13144 32 64) 24 8) (MInt2Float (extract v_13148 32 64) 24 8))) (MInt2Float (extract v_13153 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13144 64 96) 24 8) (MInt2Float (extract v_13148 64 96) 24 8))) (MInt2Float (extract v_13153 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13144 96 128) 24 8) (MInt2Float (extract v_13148 96 128) 24 8))) (MInt2Float (extract v_13153 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13144 128 160) 24 8) (MInt2Float (extract v_13148 128 160) 24 8))) (MInt2Float (extract v_13153 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13144 160 192) 24 8) (MInt2Float (extract v_13148 160 192) 24 8))) (MInt2Float (extract v_13153 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13144 192 224) 24 8) (MInt2Float (extract v_13148 192 224) 24 8))) (MInt2Float (extract v_13153 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13144 224 256) 24 8) (MInt2Float (extract v_13148 224 256) 24 8))) (MInt2Float (extract v_13153 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
