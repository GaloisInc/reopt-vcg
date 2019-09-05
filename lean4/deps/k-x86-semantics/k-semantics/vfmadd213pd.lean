def vfmadd213pd1 : instruction :=
  definst "vfmadd213pd" $ do
    pattern fun (v_2549 : reg (bv 128)) (v_2550 : reg (bv 128)) (v_2551 : reg (bv 128)) => do
      v_4334 <- getRegister v_2550;
      v_4337 <- getRegister v_2551;
      v_4341 <- getRegister v_2549;
      setRegister (lhs.of_reg v_2551) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4334 0 64) 53 11) (MInt2Float (extract v_4337 0 64) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_4341 0 64) 53 11)) 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4334 64 128) 53 11) (MInt2Float (extract v_4337 64 128) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_4341 64 128) 53 11)) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2559 : reg (bv 256)) (v_2560 : reg (bv 256)) (v_2561 : reg (bv 256)) => do
      v_4368 <- getRegister v_2560;
      v_4370 <- getRegister v_2559;
      v_4372 <- getRegister v_2561;
      setRegister (lhs.of_reg v_2561) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4368 0 64) (extract v_4370 0 64) (extract v_4372 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4368 64 128) (extract v_4370 64 128) (extract v_4372 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4368 128 192) (extract v_4370 128 192) (extract v_4372 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4368 192 256) (extract v_4370 192 256) (extract v_4372 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2543 : Mem) (v_2544 : reg (bv 128)) (v_2545 : reg (bv 128)) => do
      v_10342 <- getRegister v_2544;
      v_10345 <- getRegister v_2545;
      v_10349 <- evaluateAddress v_2543;
      v_10350 <- load v_10349 16;
      setRegister (lhs.of_reg v_2545) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10342 0 64) 53 11) (MInt2Float (extract v_10345 0 64) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_10350 0 64) 53 11)) 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10342 64 128) 53 11) (MInt2Float (extract v_10345 64 128) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_10350 64 128) 53 11)) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2554 : Mem) (v_2555 : reg (bv 256)) (v_2556 : reg (bv 256)) => do
      v_10372 <- getRegister v_2555;
      v_10374 <- evaluateAddress v_2554;
      v_10375 <- load v_10374 32;
      v_10377 <- getRegister v_2556;
      setRegister (lhs.of_reg v_2556) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10372 0 64) (extract v_10375 0 64) (extract v_10377 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10372 64 128) (extract v_10375 64 128) (extract v_10377 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10372 128 192) (extract v_10375 128 192) (extract v_10377 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10372 192 256) (extract v_10375 192 256) (extract v_10377 192 256)))));
      pure ()
    pat_end
