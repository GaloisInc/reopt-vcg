def vfnmsub132pd1 : instruction :=
  definst "vfnmsub132pd" $ do
    pattern fun (v_3276 : reg (bv 128)) (v_3277 : reg (bv 128)) (v_3278 : reg (bv 128)) => do
      v_7241 <- getRegister v_3278;
      v_7244 <- getRegister v_3276;
      v_7249 <- getRegister v_3277;
      setRegister (lhs.of_reg v_3278) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7241 0 64) 53 11) (MInt2Float (extract v_7244 0 64) 53 11))) (MInt2Float (extract v_7249 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7241 64 128) 53 11) (MInt2Float (extract v_7244 64 128) 53 11))) (MInt2Float (extract v_7249 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3288 : reg (bv 256)) (v_3289 : reg (bv 256)) (v_3290 : reg (bv 256)) => do
      v_7271 <- getRegister v_3290;
      v_7274 <- getRegister v_3288;
      v_7279 <- getRegister v_3289;
      setRegister (lhs.of_reg v_3290) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7271 0 64) 53 11) (MInt2Float (extract v_7274 0 64) 53 11))) (MInt2Float (extract v_7279 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7271 64 128) 53 11) (MInt2Float (extract v_7274 64 128) 53 11))) (MInt2Float (extract v_7279 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7271 128 192) 53 11) (MInt2Float (extract v_7274 128 192) 53 11))) (MInt2Float (extract v_7279 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7271 192 256) 53 11) (MInt2Float (extract v_7274 192 256) 53 11))) (MInt2Float (extract v_7279 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_3273 : Mem) (v_3271 : reg (bv 128)) (v_3272 : reg (bv 128)) => do
      v_12928 <- getRegister v_3272;
      v_12931 <- evaluateAddress v_3273;
      v_12932 <- load v_12931 16;
      v_12937 <- getRegister v_3271;
      setRegister (lhs.of_reg v_3272) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_12928 0 64) 53 11) (MInt2Float (extract v_12932 0 64) 53 11))) (MInt2Float (extract v_12937 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_12928 64 128) 53 11) (MInt2Float (extract v_12932 64 128) 53 11))) (MInt2Float (extract v_12937 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3282 : Mem) (v_3283 : reg (bv 256)) (v_3284 : reg (bv 256)) => do
      v_12954 <- getRegister v_3284;
      v_12957 <- evaluateAddress v_3282;
      v_12958 <- load v_12957 32;
      v_12963 <- getRegister v_3283;
      setRegister (lhs.of_reg v_3284) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_12954 0 64) 53 11) (MInt2Float (extract v_12958 0 64) 53 11))) (MInt2Float (extract v_12963 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_12954 64 128) 53 11) (MInt2Float (extract v_12958 64 128) 53 11))) (MInt2Float (extract v_12963 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_12954 128 192) 53 11) (MInt2Float (extract v_12958 128 192) 53 11))) (MInt2Float (extract v_12963 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_12954 192 256) 53 11) (MInt2Float (extract v_12958 192 256) 53 11))) (MInt2Float (extract v_12963 192 256) 53 11)) 64))));
      pure ()
    pat_end
