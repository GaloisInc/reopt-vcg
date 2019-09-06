def vfnmsub213pd1 : instruction :=
  definst "vfnmsub213pd" $ do
    pattern fun (v_3431 : reg (bv 128)) (v_3432 : reg (bv 128)) (v_3433 : reg (bv 128)) => do
      v_7617 <- getRegister v_3432;
      v_7620 <- getRegister v_3433;
      v_7625 <- getRegister v_3431;
      setRegister (lhs.of_reg v_3433) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7617 0 64) 53 11) (MInt2Float (extract v_7620 0 64) 53 11))) (MInt2Float (extract v_7625 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7617 64 128) 53 11) (MInt2Float (extract v_7620 64 128) 53 11))) (MInt2Float (extract v_7625 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3445 : reg (bv 256)) (v_3446 : reg (bv 256)) (v_3447 : reg (bv 256)) => do
      v_7647 <- getRegister v_3446;
      v_7650 <- getRegister v_3447;
      v_7655 <- getRegister v_3445;
      setRegister (lhs.of_reg v_3447) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7647 0 64) 53 11) (MInt2Float (extract v_7650 0 64) 53 11))) (MInt2Float (extract v_7655 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7647 64 128) 53 11) (MInt2Float (extract v_7650 64 128) 53 11))) (MInt2Float (extract v_7655 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7647 128 192) 53 11) (MInt2Float (extract v_7650 128 192) 53 11))) (MInt2Float (extract v_7655 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7647 192 256) 53 11) (MInt2Float (extract v_7650 192 256) 53 11))) (MInt2Float (extract v_7655 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_3428 : Mem) (v_3426 : reg (bv 128)) (v_3427 : reg (bv 128)) => do
      v_13295 <- getRegister v_3426;
      v_13298 <- getRegister v_3427;
      v_13303 <- evaluateAddress v_3428;
      v_13304 <- load v_13303 16;
      setRegister (lhs.of_reg v_3427) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13295 0 64) 53 11) (MInt2Float (extract v_13298 0 64) 53 11))) (MInt2Float (extract v_13304 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13295 64 128) 53 11) (MInt2Float (extract v_13298 64 128) 53 11))) (MInt2Float (extract v_13304 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3437 : Mem) (v_3440 : reg (bv 256)) (v_3441 : reg (bv 256)) => do
      v_13321 <- getRegister v_3440;
      v_13324 <- getRegister v_3441;
      v_13329 <- evaluateAddress v_3437;
      v_13330 <- load v_13329 32;
      setRegister (lhs.of_reg v_3441) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13321 0 64) 53 11) (MInt2Float (extract v_13324 0 64) 53 11))) (MInt2Float (extract v_13330 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13321 64 128) 53 11) (MInt2Float (extract v_13324 64 128) 53 11))) (MInt2Float (extract v_13330 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13321 128 192) 53 11) (MInt2Float (extract v_13324 128 192) 53 11))) (MInt2Float (extract v_13330 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13321 192 256) 53 11) (MInt2Float (extract v_13324 192 256) 53 11))) (MInt2Float (extract v_13330 192 256) 53 11)) 64))));
      pure ()
    pat_end
