def vfnmsub213pd1 : instruction :=
  definst "vfnmsub213pd" $ do
    pattern fun (v_3407 : reg (bv 128)) (v_3408 : reg (bv 128)) (v_3409 : reg (bv 128)) => do
      v_7590 <- getRegister v_3408;
      v_7593 <- getRegister v_3409;
      v_7598 <- getRegister v_3407;
      setRegister (lhs.of_reg v_3409) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7590 0 64) 53 11) (MInt2Float (extract v_7593 0 64) 53 11))) (MInt2Float (extract v_7598 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7590 64 128) 53 11) (MInt2Float (extract v_7593 64 128) 53 11))) (MInt2Float (extract v_7598 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3417 : reg (bv 256)) (v_3418 : reg (bv 256)) (v_3419 : reg (bv 256)) => do
      v_7620 <- getRegister v_3418;
      v_7623 <- getRegister v_3419;
      v_7628 <- getRegister v_3417;
      setRegister (lhs.of_reg v_3419) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7620 0 64) 53 11) (MInt2Float (extract v_7623 0 64) 53 11))) (MInt2Float (extract v_7628 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7620 64 128) 53 11) (MInt2Float (extract v_7623 64 128) 53 11))) (MInt2Float (extract v_7628 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7620 128 192) 53 11) (MInt2Float (extract v_7623 128 192) 53 11))) (MInt2Float (extract v_7628 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7620 192 256) 53 11) (MInt2Float (extract v_7623 192 256) 53 11))) (MInt2Float (extract v_7628 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_3401 : Mem) (v_3402 : reg (bv 128)) (v_3403 : reg (bv 128)) => do
      v_13268 <- getRegister v_3402;
      v_13271 <- getRegister v_3403;
      v_13276 <- evaluateAddress v_3401;
      v_13277 <- load v_13276 16;
      setRegister (lhs.of_reg v_3403) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13268 0 64) 53 11) (MInt2Float (extract v_13271 0 64) 53 11))) (MInt2Float (extract v_13277 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13268 64 128) 53 11) (MInt2Float (extract v_13271 64 128) 53 11))) (MInt2Float (extract v_13277 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3412 : Mem) (v_3413 : reg (bv 256)) (v_3414 : reg (bv 256)) => do
      v_13294 <- getRegister v_3413;
      v_13297 <- getRegister v_3414;
      v_13302 <- evaluateAddress v_3412;
      v_13303 <- load v_13302 32;
      setRegister (lhs.of_reg v_3414) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13294 0 64) 53 11) (MInt2Float (extract v_13297 0 64) 53 11))) (MInt2Float (extract v_13303 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13294 64 128) 53 11) (MInt2Float (extract v_13297 64 128) 53 11))) (MInt2Float (extract v_13303 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13294 128 192) 53 11) (MInt2Float (extract v_13297 128 192) 53 11))) (MInt2Float (extract v_13303 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13294 192 256) 53 11) (MInt2Float (extract v_13297 192 256) 53 11))) (MInt2Float (extract v_13303 192 256) 53 11)) 64))));
      pure ()
    pat_end
