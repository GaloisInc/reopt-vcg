def vfmadd231pd1 : instruction :=
  definst "vfmadd231pd" $ do
    pattern fun (v_2639 : reg (bv 128)) (v_2640 : reg (bv 128)) (v_2641 : reg (bv 128)) => do
      v_4619 <- getRegister v_2640;
      v_4622 <- getRegister v_2639;
      v_4626 <- getRegister v_2641;
      setRegister (lhs.of_reg v_2641) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4619 0 64) 53 11) (MInt2Float (extract v_4622 0 64) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_4626 0 64) 53 11)) 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4619 64 128) 53 11) (MInt2Float (extract v_4622 64 128) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_4626 64 128) 53 11)) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2653 : reg (bv 256)) (v_2654 : reg (bv 256)) (v_2655 : reg (bv 256)) => do
      v_4653 <- getRegister v_2654;
      v_4655 <- getRegister v_2655;
      v_4657 <- getRegister v_2653;
      setRegister (lhs.of_reg v_2655) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4653 0 64) (extract v_4655 0 64) (extract v_4657 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4653 64 128) (extract v_4655 64 128) (extract v_4657 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4653 128 192) (extract v_4655 128 192) (extract v_4657 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4653 192 256) (extract v_4655 192 256) (extract v_4657 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2636 : Mem) (v_2634 : reg (bv 128)) (v_2635 : reg (bv 128)) => do
      v_10601 <- getRegister v_2634;
      v_10604 <- evaluateAddress v_2636;
      v_10605 <- load v_10604 16;
      v_10609 <- getRegister v_2635;
      setRegister (lhs.of_reg v_2635) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10601 0 64) 53 11) (MInt2Float (extract v_10605 0 64) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_10609 0 64) 53 11)) 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10601 64 128) 53 11) (MInt2Float (extract v_10605 64 128) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_10609 64 128) 53 11)) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2645 : Mem) (v_2648 : reg (bv 256)) (v_2649 : reg (bv 256)) => do
      v_10631 <- getRegister v_2648;
      v_10633 <- getRegister v_2649;
      v_10635 <- evaluateAddress v_2645;
      v_10636 <- load v_10635 32;
      setRegister (lhs.of_reg v_2649) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10631 0 64) (extract v_10633 0 64) (extract v_10636 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10631 64 128) (extract v_10633 64 128) (extract v_10636 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10631 128 192) (extract v_10633 128 192) (extract v_10636 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10631 192 256) (extract v_10633 192 256) (extract v_10636 192 256)))));
      pure ()
    pat_end
