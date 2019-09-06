def vfmadd213pd1 : instruction :=
  definst "vfmadd213pd" $ do
    pattern fun (v_2573 : reg (bv 128)) (v_2574 : reg (bv 128)) (v_2575 : reg (bv 128)) => do
      v_4361 <- getRegister v_2574;
      v_4364 <- getRegister v_2575;
      v_4368 <- getRegister v_2573;
      setRegister (lhs.of_reg v_2575) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4361 0 64) 53 11) (MInt2Float (extract v_4364 0 64) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_4368 0 64) 53 11)) 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4361 64 128) 53 11) (MInt2Float (extract v_4364 64 128) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_4368 64 128) 53 11)) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2587 : reg (bv 256)) (v_2588 : reg (bv 256)) (v_2589 : reg (bv 256)) => do
      v_4395 <- getRegister v_2588;
      v_4397 <- getRegister v_2587;
      v_4399 <- getRegister v_2589;
      setRegister (lhs.of_reg v_2589) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4395 0 64) (extract v_4397 0 64) (extract v_4399 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4395 64 128) (extract v_4397 64 128) (extract v_4399 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4395 128 192) (extract v_4397 128 192) (extract v_4399 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4395 192 256) (extract v_4397 192 256) (extract v_4399 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2570 : Mem) (v_2568 : reg (bv 128)) (v_2569 : reg (bv 128)) => do
      v_10369 <- getRegister v_2568;
      v_10372 <- getRegister v_2569;
      v_10376 <- evaluateAddress v_2570;
      v_10377 <- load v_10376 16;
      setRegister (lhs.of_reg v_2569) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10369 0 64) 53 11) (MInt2Float (extract v_10372 0 64) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_10377 0 64) 53 11)) 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10369 64 128) 53 11) (MInt2Float (extract v_10372 64 128) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_10377 64 128) 53 11)) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2579 : Mem) (v_2582 : reg (bv 256)) (v_2583 : reg (bv 256)) => do
      v_10399 <- getRegister v_2582;
      v_10401 <- evaluateAddress v_2579;
      v_10402 <- load v_10401 32;
      v_10404 <- getRegister v_2583;
      setRegister (lhs.of_reg v_2583) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10399 0 64) (extract v_10402 0 64) (extract v_10404 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10399 64 128) (extract v_10402 64 128) (extract v_10404 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10399 128 192) (extract v_10402 128 192) (extract v_10404 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10399 192 256) (extract v_10402 192 256) (extract v_10404 192 256)))));
      pure ()
    pat_end
