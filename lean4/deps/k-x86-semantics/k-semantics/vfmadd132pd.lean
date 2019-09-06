def vfmadd132pd1 : instruction :=
  definst "vfmadd132pd" $ do
    pattern fun (v_2507 : reg (bv 128)) (v_2508 : reg (bv 128)) (v_2509 : reg (bv 128)) => do
      v_4128 <- getRegister v_2509;
      v_4131 <- getRegister v_2507;
      v_4135 <- getRegister v_2508;
      setRegister (lhs.of_reg v_2509) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4128 0 64) 53 11) (MInt2Float (extract v_4131 0 64) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_4135 0 64) 53 11)) 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4128 64 128) 53 11) (MInt2Float (extract v_4131 64 128) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_4135 64 128) 53 11)) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2521 : reg (bv 256)) (v_2522 : reg (bv 256)) (v_2523 : reg (bv 256)) => do
      v_4162 <- getRegister v_2523;
      v_4164 <- getRegister v_2522;
      v_4166 <- getRegister v_2521;
      setRegister (lhs.of_reg v_2523) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4162 0 64) (extract v_4164 0 64) (extract v_4166 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4162 64 128) (extract v_4164 64 128) (extract v_4166 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4162 128 192) (extract v_4164 128 192) (extract v_4166 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4162 192 256) (extract v_4164 192 256) (extract v_4166 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2504 : Mem) (v_2502 : reg (bv 128)) (v_2503 : reg (bv 128)) => do
      v_10162 <- getRegister v_2503;
      v_10165 <- evaluateAddress v_2504;
      v_10166 <- load v_10165 16;
      v_10170 <- getRegister v_2502;
      setRegister (lhs.of_reg v_2503) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10162 0 64) 53 11) (MInt2Float (extract v_10166 0 64) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_10170 0 64) 53 11)) 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10162 64 128) 53 11) (MInt2Float (extract v_10166 64 128) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_10170 64 128) 53 11)) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2513 : Mem) (v_2516 : reg (bv 256)) (v_2517 : reg (bv 256)) => do
      v_10192 <- getRegister v_2517;
      v_10194 <- getRegister v_2516;
      v_10196 <- evaluateAddress v_2513;
      v_10197 <- load v_10196 32;
      setRegister (lhs.of_reg v_2517) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10192 0 64) (extract v_10194 0 64) (extract v_10197 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10192 64 128) (extract v_10194 64 128) (extract v_10197 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10192 128 192) (extract v_10194 128 192) (extract v_10197 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10192 192 256) (extract v_10194 192 256) (extract v_10197 192 256)))));
      pure ()
    pat_end
