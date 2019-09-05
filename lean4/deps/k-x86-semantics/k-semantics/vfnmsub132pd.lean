def vfnmsub132pd1 : instruction :=
  definst "vfnmsub132pd" $ do
    pattern fun (v_3341 : reg (bv 128)) (v_3342 : reg (bv 128)) (v_3343 : reg (bv 128)) => do
      v_7318 <- getRegister v_3343;
      v_7321 <- getRegister v_3341;
      v_7326 <- getRegister v_3342;
      setRegister (lhs.of_reg v_3343) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7318 0 64) 53 11) (MInt2Float (extract v_7321 0 64) 53 11))) (MInt2Float (extract v_7326 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7318 64 128) 53 11) (MInt2Float (extract v_7321 64 128) 53 11))) (MInt2Float (extract v_7326 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3351 : reg (bv 256)) (v_3352 : reg (bv 256)) (v_3353 : reg (bv 256)) => do
      v_7348 <- getRegister v_3353;
      v_7351 <- getRegister v_3351;
      v_7356 <- getRegister v_3352;
      setRegister (lhs.of_reg v_3353) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7348 0 64) 53 11) (MInt2Float (extract v_7351 0 64) 53 11))) (MInt2Float (extract v_7356 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7348 64 128) 53 11) (MInt2Float (extract v_7351 64 128) 53 11))) (MInt2Float (extract v_7356 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7348 128 192) 53 11) (MInt2Float (extract v_7351 128 192) 53 11))) (MInt2Float (extract v_7356 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7348 192 256) 53 11) (MInt2Float (extract v_7351 192 256) 53 11))) (MInt2Float (extract v_7356 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_3335 : Mem) (v_3336 : reg (bv 128)) (v_3337 : reg (bv 128)) => do
      v_13022 <- getRegister v_3337;
      v_13025 <- evaluateAddress v_3335;
      v_13026 <- load v_13025 16;
      v_13031 <- getRegister v_3336;
      setRegister (lhs.of_reg v_3337) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13022 0 64) 53 11) (MInt2Float (extract v_13026 0 64) 53 11))) (MInt2Float (extract v_13031 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13022 64 128) 53 11) (MInt2Float (extract v_13026 64 128) 53 11))) (MInt2Float (extract v_13031 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3346 : Mem) (v_3347 : reg (bv 256)) (v_3348 : reg (bv 256)) => do
      v_13048 <- getRegister v_3348;
      v_13051 <- evaluateAddress v_3346;
      v_13052 <- load v_13051 32;
      v_13057 <- getRegister v_3347;
      setRegister (lhs.of_reg v_3348) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13048 0 64) 53 11) (MInt2Float (extract v_13052 0 64) 53 11))) (MInt2Float (extract v_13057 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13048 64 128) 53 11) (MInt2Float (extract v_13052 64 128) 53 11))) (MInt2Float (extract v_13057 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13048 128 192) 53 11) (MInt2Float (extract v_13052 128 192) 53 11))) (MInt2Float (extract v_13057 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13048 192 256) 53 11) (MInt2Float (extract v_13052 192 256) 53 11))) (MInt2Float (extract v_13057 192 256) 53 11)) 64))));
      pure ()
    pat_end
