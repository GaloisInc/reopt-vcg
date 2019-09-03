def vfmadd213pd1 : instruction :=
  definst "vfmadd213pd" $ do
    pattern fun (v_2484 : reg (bv 128)) (v_2485 : reg (bv 128)) (v_2486 : reg (bv 128)) => do
      v_4274 <- getRegister v_2485;
      v_4277 <- getRegister v_2486;
      v_4281 <- getRegister v_2484;
      setRegister (lhs.of_reg v_2486) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4274 0 64) 53 11) (MInt2Float (extract v_4277 0 64) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MInt2Float (extract v_4281 0 64) 53 11)) 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4274 64 128) 53 11) (MInt2Float (extract v_4277 64 128) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MInt2Float (extract v_4281 64 128) 53 11)) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2496 : reg (bv 256)) (v_2497 : reg (bv 256)) (v_2498 : reg (bv 256)) => do
      v_4308 <- getRegister v_2497;
      v_4310 <- getRegister v_2496;
      v_4312 <- getRegister v_2498;
      setRegister (lhs.of_reg v_2498) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4308 0 64) (extract v_4310 0 64) (extract v_4312 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4308 64 128) (extract v_4310 64 128) (extract v_4312 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4308 128 192) (extract v_4310 128 192) (extract v_4312 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4308 192 256) (extract v_4310 192 256) (extract v_4312 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2481 : Mem) (v_2479 : reg (bv 128)) (v_2480 : reg (bv 128)) => do
      v_10265 <- getRegister v_2479;
      v_10268 <- getRegister v_2480;
      v_10272 <- evaluateAddress v_2481;
      v_10273 <- load v_10272 16;
      setRegister (lhs.of_reg v_2480) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10265 0 64) 53 11) (MInt2Float (extract v_10268 0 64) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MInt2Float (extract v_10273 0 64) 53 11)) 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10265 64 128) 53 11) (MInt2Float (extract v_10268 64 128) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MInt2Float (extract v_10273 64 128) 53 11)) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2490 : Mem) (v_2491 : reg (bv 256)) (v_2492 : reg (bv 256)) => do
      v_10295 <- getRegister v_2491;
      v_10297 <- evaluateAddress v_2490;
      v_10298 <- load v_10297 32;
      v_10300 <- getRegister v_2492;
      setRegister (lhs.of_reg v_2492) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10295 0 64) (extract v_10298 0 64) (extract v_10300 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10295 64 128) (extract v_10298 64 128) (extract v_10300 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10295 128 192) (extract v_10298 128 192) (extract v_10300 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10295 192 256) (extract v_10298 192 256) (extract v_10300 192 256)))));
      pure ()
    pat_end
