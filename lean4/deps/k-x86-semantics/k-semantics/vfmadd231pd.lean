def vfmadd231pd1 : instruction :=
  definst "vfmadd231pd" $ do
    pattern fun (v_2615 : reg (bv 128)) (v_2616 : reg (bv 128)) (v_2617 : reg (bv 128)) => do
      v_4592 <- getRegister v_2616;
      v_4595 <- getRegister v_2615;
      v_4599 <- getRegister v_2617;
      setRegister (lhs.of_reg v_2617) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4592 0 64) 53 11) (MInt2Float (extract v_4595 0 64) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_4599 0 64) 53 11)) 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4592 64 128) 53 11) (MInt2Float (extract v_4595 64 128) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_4599 64 128) 53 11)) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2625 : reg (bv 256)) (v_2626 : reg (bv 256)) (v_2627 : reg (bv 256)) => do
      v_4626 <- getRegister v_2626;
      v_4628 <- getRegister v_2627;
      v_4630 <- getRegister v_2625;
      setRegister (lhs.of_reg v_2627) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4626 0 64) (extract v_4628 0 64) (extract v_4630 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4626 64 128) (extract v_4628 64 128) (extract v_4630 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4626 128 192) (extract v_4628 128 192) (extract v_4630 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4626 192 256) (extract v_4628 192 256) (extract v_4630 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2609 : Mem) (v_2610 : reg (bv 128)) (v_2611 : reg (bv 128)) => do
      v_10574 <- getRegister v_2610;
      v_10577 <- evaluateAddress v_2609;
      v_10578 <- load v_10577 16;
      v_10582 <- getRegister v_2611;
      setRegister (lhs.of_reg v_2611) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10574 0 64) 53 11) (MInt2Float (extract v_10578 0 64) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_10582 0 64) 53 11)) 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10574 64 128) 53 11) (MInt2Float (extract v_10578 64 128) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_10582 64 128) 53 11)) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2620 : Mem) (v_2621 : reg (bv 256)) (v_2622 : reg (bv 256)) => do
      v_10604 <- getRegister v_2621;
      v_10606 <- getRegister v_2622;
      v_10608 <- evaluateAddress v_2620;
      v_10609 <- load v_10608 32;
      setRegister (lhs.of_reg v_2622) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10604 0 64) (extract v_10606 0 64) (extract v_10609 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10604 64 128) (extract v_10606 64 128) (extract v_10609 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10604 128 192) (extract v_10606 128 192) (extract v_10609 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10604 192 256) (extract v_10606 192 256) (extract v_10609 192 256)))));
      pure ()
    pat_end
