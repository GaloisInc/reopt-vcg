def vfmadd231pd1 : instruction :=
  definst "vfmadd231pd" $ do
    pattern fun (v_2550 : reg (bv 128)) (v_2551 : reg (bv 128)) (v_2552 : reg (bv 128)) => do
      v_4532 <- getRegister v_2551;
      v_4535 <- getRegister v_2550;
      v_4539 <- getRegister v_2552;
      setRegister (lhs.of_reg v_2552) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4532 0 64) 53 11) (MInt2Float (extract v_4535 0 64) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MInt2Float (extract v_4539 0 64) 53 11)) 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4532 64 128) 53 11) (MInt2Float (extract v_4535 64 128) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MInt2Float (extract v_4539 64 128) 53 11)) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2562 : reg (bv 256)) (v_2563 : reg (bv 256)) (v_2564 : reg (bv 256)) => do
      v_4566 <- getRegister v_2563;
      v_4568 <- getRegister v_2564;
      v_4570 <- getRegister v_2562;
      setRegister (lhs.of_reg v_2564) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4566 0 64) (extract v_4568 0 64) (extract v_4570 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4566 64 128) (extract v_4568 64 128) (extract v_4570 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4566 128 192) (extract v_4568 128 192) (extract v_4570 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4566 192 256) (extract v_4568 192 256) (extract v_4570 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2547 : Mem) (v_2545 : reg (bv 128)) (v_2546 : reg (bv 128)) => do
      v_10497 <- getRegister v_2545;
      v_10500 <- evaluateAddress v_2547;
      v_10501 <- load v_10500 16;
      v_10505 <- getRegister v_2546;
      setRegister (lhs.of_reg v_2546) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10497 0 64) 53 11) (MInt2Float (extract v_10501 0 64) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MInt2Float (extract v_10505 0 64) 53 11)) 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10497 64 128) 53 11) (MInt2Float (extract v_10501 64 128) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MInt2Float (extract v_10505 64 128) 53 11)) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2556 : Mem) (v_2557 : reg (bv 256)) (v_2558 : reg (bv 256)) => do
      v_10527 <- getRegister v_2557;
      v_10529 <- getRegister v_2558;
      v_10531 <- evaluateAddress v_2556;
      v_10532 <- load v_10531 32;
      setRegister (lhs.of_reg v_2558) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10527 0 64) (extract v_10529 0 64) (extract v_10532 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10527 64 128) (extract v_10529 64 128) (extract v_10532 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10527 128 192) (extract v_10529 128 192) (extract v_10532 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10527 192 256) (extract v_10529 192 256) (extract v_10532 192 256)))));
      pure ()
    pat_end
