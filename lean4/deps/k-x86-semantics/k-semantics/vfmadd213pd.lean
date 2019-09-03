def vfmadd213pd1 : instruction :=
  definst "vfmadd213pd" $ do
    pattern fun (v_2497 : reg (bv 128)) (v_2498 : reg (bv 128)) (v_2499 : reg (bv 128)) => do
      v_4556 <- getRegister v_2498;
      v_4557 <- eval (extract v_4556 0 64);
      v_4565 <- getRegister v_2499;
      v_4566 <- eval (extract v_4565 0 64);
      v_4575 <- getRegister v_2497;
      v_4576 <- eval (extract v_4575 0 64);
      v_4589 <- eval (extract v_4556 64 128);
      v_4597 <- eval (extract v_4565 64 128);
      v_4606 <- eval (extract v_4575 64 128);
      setRegister (lhs.of_reg v_2499) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4557 0 1)) (uvalueMInt (extract v_4557 1 12)) (uvalueMInt (extract v_4557 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4566 0 1)) (uvalueMInt (extract v_4566 1 12)) (uvalueMInt (extract v_4566 12 64)))) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4576 0 1)) (uvalueMInt (extract v_4576 1 12)) (uvalueMInt (extract v_4576 12 64)))) 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4589 0 1)) (uvalueMInt (extract v_4589 1 12)) (uvalueMInt (extract v_4589 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4597 0 1)) (uvalueMInt (extract v_4597 1 12)) (uvalueMInt (extract v_4597 12 64)))) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4606 0 1)) (uvalueMInt (extract v_4606 1 12)) (uvalueMInt (extract v_4606 12 64)))) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2508 : reg (bv 256)) (v_2509 : reg (bv 256)) (v_2510 : reg (bv 256)) => do
      v_4626 <- getRegister v_2509;
      v_4628 <- getRegister v_2508;
      v_4630 <- getRegister v_2510;
      setRegister (lhs.of_reg v_2510) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4626 0 64) (extract v_4628 0 64) (extract v_4630 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4626 64 128) (extract v_4628 64 128) (extract v_4630 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4626 128 192) (extract v_4628 128 192) (extract v_4630 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4626 192 256) (extract v_4628 192 256) (extract v_4630 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2494 : Mem) (v_2492 : reg (bv 128)) (v_2493 : reg (bv 128)) => do
      v_15479 <- getRegister v_2492;
      v_15480 <- eval (extract v_15479 0 64);
      v_15488 <- getRegister v_2493;
      v_15489 <- eval (extract v_15488 0 64);
      v_15498 <- evaluateAddress v_2494;
      v_15499 <- load v_15498 16;
      v_15500 <- eval (extract v_15499 0 64);
      v_15513 <- eval (extract v_15479 64 128);
      v_15521 <- eval (extract v_15488 64 128);
      v_15530 <- eval (extract v_15499 64 128);
      setRegister (lhs.of_reg v_2493) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_15480 0 1)) (uvalueMInt (extract v_15480 1 12)) (uvalueMInt (extract v_15480 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_15489 0 1)) (uvalueMInt (extract v_15489 1 12)) (uvalueMInt (extract v_15489 12 64)))) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MIntToFloatImpl 53 11 (uvalueMInt (extract v_15500 0 1)) (uvalueMInt (extract v_15500 1 12)) (uvalueMInt (extract v_15500 12 64)))) 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_15513 0 1)) (uvalueMInt (extract v_15513 1 12)) (uvalueMInt (extract v_15513 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_15521 0 1)) (uvalueMInt (extract v_15521 1 12)) (uvalueMInt (extract v_15521 12 64)))) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MIntToFloatImpl 53 11 (uvalueMInt (extract v_15530 0 1)) (uvalueMInt (extract v_15530 1 12)) (uvalueMInt (extract v_15530 12 64)))) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2503 : Mem) (v_2504 : reg (bv 256)) (v_2505 : reg (bv 256)) => do
      v_15545 <- getRegister v_2504;
      v_15547 <- evaluateAddress v_2503;
      v_15548 <- load v_15547 32;
      v_15550 <- getRegister v_2505;
      setRegister (lhs.of_reg v_2505) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_15545 0 64) (extract v_15548 0 64) (extract v_15550 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_15545 64 128) (extract v_15548 64 128) (extract v_15550 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_15545 128 192) (extract v_15548 128 192) (extract v_15550 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_15545 192 256) (extract v_15548 192 256) (extract v_15550 192 256)))));
      pure ()
    pat_end
