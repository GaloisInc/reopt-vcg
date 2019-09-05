def vfmadd132pd1 : instruction :=
  definst "vfmadd132pd" $ do
    pattern fun (v_2483 : reg (bv 128)) (v_2484 : reg (bv 128)) (v_2485 : reg (bv 128)) => do
      v_4101 <- getRegister v_2485;
      v_4104 <- getRegister v_2483;
      v_4108 <- getRegister v_2484;
      setRegister (lhs.of_reg v_2485) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4101 0 64) 53 11) (MInt2Float (extract v_4104 0 64) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_4108 0 64) 53 11)) 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4101 64 128) 53 11) (MInt2Float (extract v_4104 64 128) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_4108 64 128) 53 11)) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2493 : reg (bv 256)) (v_2494 : reg (bv 256)) (v_2495 : reg (bv 256)) => do
      v_4135 <- getRegister v_2495;
      v_4137 <- getRegister v_2494;
      v_4139 <- getRegister v_2493;
      setRegister (lhs.of_reg v_2495) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4135 0 64) (extract v_4137 0 64) (extract v_4139 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4135 64 128) (extract v_4137 64 128) (extract v_4139 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4135 128 192) (extract v_4137 128 192) (extract v_4139 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4135 192 256) (extract v_4137 192 256) (extract v_4139 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2477 : Mem) (v_2478 : reg (bv 128)) (v_2479 : reg (bv 128)) => do
      v_10135 <- getRegister v_2479;
      v_10138 <- evaluateAddress v_2477;
      v_10139 <- load v_10138 16;
      v_10143 <- getRegister v_2478;
      setRegister (lhs.of_reg v_2479) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10135 0 64) 53 11) (MInt2Float (extract v_10139 0 64) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_10143 0 64) 53 11)) 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10135 64 128) 53 11) (MInt2Float (extract v_10139 64 128) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_10143 64 128) 53 11)) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2488 : Mem) (v_2489 : reg (bv 256)) (v_2490 : reg (bv 256)) => do
      v_10165 <- getRegister v_2490;
      v_10167 <- getRegister v_2489;
      v_10169 <- evaluateAddress v_2488;
      v_10170 <- load v_10169 32;
      setRegister (lhs.of_reg v_2490) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10165 0 64) (extract v_10167 0 64) (extract v_10170 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10165 64 128) (extract v_10167 64 128) (extract v_10170 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10165 128 192) (extract v_10167 128 192) (extract v_10170 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10165 192 256) (extract v_10167 192 256) (extract v_10170 192 256)))));
      pure ()
    pat_end
