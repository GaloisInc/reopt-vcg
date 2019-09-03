def vfnmsub213pd1 : instruction :=
  definst "vfnmsub213pd" $ do
    pattern fun (v_3342 : reg (bv 128)) (v_3343 : reg (bv 128)) (v_3344 : reg (bv 128)) => do
      v_7513 <- getRegister v_3343;
      v_7516 <- getRegister v_3344;
      v_7521 <- getRegister v_3342;
      setRegister (lhs.of_reg v_3344) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7513 0 64) 53 11) (MInt2Float (extract v_7516 0 64) 53 11))) (MInt2Float (extract v_7521 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7513 64 128) 53 11) (MInt2Float (extract v_7516 64 128) 53 11))) (MInt2Float (extract v_7521 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3354 : reg (bv 256)) (v_3355 : reg (bv 256)) (v_3356 : reg (bv 256)) => do
      v_7543 <- getRegister v_3355;
      v_7546 <- getRegister v_3356;
      v_7551 <- getRegister v_3354;
      setRegister (lhs.of_reg v_3356) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7543 0 64) 53 11) (MInt2Float (extract v_7546 0 64) 53 11))) (MInt2Float (extract v_7551 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7543 64 128) 53 11) (MInt2Float (extract v_7546 64 128) 53 11))) (MInt2Float (extract v_7551 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7543 128 192) 53 11) (MInt2Float (extract v_7546 128 192) 53 11))) (MInt2Float (extract v_7551 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7543 192 256) 53 11) (MInt2Float (extract v_7546 192 256) 53 11))) (MInt2Float (extract v_7551 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_3339 : Mem) (v_3337 : reg (bv 128)) (v_3338 : reg (bv 128)) => do
      v_13174 <- getRegister v_3337;
      v_13177 <- getRegister v_3338;
      v_13182 <- evaluateAddress v_3339;
      v_13183 <- load v_13182 16;
      setRegister (lhs.of_reg v_3338) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13174 0 64) 53 11) (MInt2Float (extract v_13177 0 64) 53 11))) (MInt2Float (extract v_13183 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13174 64 128) 53 11) (MInt2Float (extract v_13177 64 128) 53 11))) (MInt2Float (extract v_13183 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3348 : Mem) (v_3349 : reg (bv 256)) (v_3350 : reg (bv 256)) => do
      v_13200 <- getRegister v_3349;
      v_13203 <- getRegister v_3350;
      v_13208 <- evaluateAddress v_3348;
      v_13209 <- load v_13208 32;
      setRegister (lhs.of_reg v_3350) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13200 0 64) 53 11) (MInt2Float (extract v_13203 0 64) 53 11))) (MInt2Float (extract v_13209 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13200 64 128) 53 11) (MInt2Float (extract v_13203 64 128) 53 11))) (MInt2Float (extract v_13209 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13200 128 192) 53 11) (MInt2Float (extract v_13203 128 192) 53 11))) (MInt2Float (extract v_13209 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13200 192 256) 53 11) (MInt2Float (extract v_13203 192 256) 53 11))) (MInt2Float (extract v_13209 192 256) 53 11)) 64))));
      pure ()
    pat_end
