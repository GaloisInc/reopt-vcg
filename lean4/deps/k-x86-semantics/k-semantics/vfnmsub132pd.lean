def vfnmsub132pd1 : instruction :=
  definst "vfnmsub132pd" $ do
    pattern fun (v_3365 : reg (bv 128)) (v_3366 : reg (bv 128)) (v_3367 : reg (bv 128)) => do
      v_7345 <- getRegister v_3367;
      v_7348 <- getRegister v_3365;
      v_7353 <- getRegister v_3366;
      setRegister (lhs.of_reg v_3367) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7345 0 64) 53 11) (MInt2Float (extract v_7348 0 64) 53 11))) (MInt2Float (extract v_7353 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7345 64 128) 53 11) (MInt2Float (extract v_7348 64 128) 53 11))) (MInt2Float (extract v_7353 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3379 : reg (bv 256)) (v_3380 : reg (bv 256)) (v_3381 : reg (bv 256)) => do
      v_7375 <- getRegister v_3381;
      v_7378 <- getRegister v_3379;
      v_7383 <- getRegister v_3380;
      setRegister (lhs.of_reg v_3381) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7375 0 64) 53 11) (MInt2Float (extract v_7378 0 64) 53 11))) (MInt2Float (extract v_7383 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7375 64 128) 53 11) (MInt2Float (extract v_7378 64 128) 53 11))) (MInt2Float (extract v_7383 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7375 128 192) 53 11) (MInt2Float (extract v_7378 128 192) 53 11))) (MInt2Float (extract v_7383 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7375 192 256) 53 11) (MInt2Float (extract v_7378 192 256) 53 11))) (MInt2Float (extract v_7383 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_3362 : Mem) (v_3360 : reg (bv 128)) (v_3361 : reg (bv 128)) => do
      v_13049 <- getRegister v_3361;
      v_13052 <- evaluateAddress v_3362;
      v_13053 <- load v_13052 16;
      v_13058 <- getRegister v_3360;
      setRegister (lhs.of_reg v_3361) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13049 0 64) 53 11) (MInt2Float (extract v_13053 0 64) 53 11))) (MInt2Float (extract v_13058 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13049 64 128) 53 11) (MInt2Float (extract v_13053 64 128) 53 11))) (MInt2Float (extract v_13058 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3371 : Mem) (v_3374 : reg (bv 256)) (v_3375 : reg (bv 256)) => do
      v_13075 <- getRegister v_3375;
      v_13078 <- evaluateAddress v_3371;
      v_13079 <- load v_13078 32;
      v_13084 <- getRegister v_3374;
      setRegister (lhs.of_reg v_3375) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13075 0 64) 53 11) (MInt2Float (extract v_13079 0 64) 53 11))) (MInt2Float (extract v_13084 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13075 64 128) 53 11) (MInt2Float (extract v_13079 64 128) 53 11))) (MInt2Float (extract v_13084 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13075 128 192) 53 11) (MInt2Float (extract v_13079 128 192) 53 11))) (MInt2Float (extract v_13084 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13075 192 256) 53 11) (MInt2Float (extract v_13079 192 256) 53 11))) (MInt2Float (extract v_13084 192 256) 53 11)) 64))));
      pure ()
    pat_end
