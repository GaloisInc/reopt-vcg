def vfmadd132pd1 : instruction :=
  definst "vfmadd132pd" $ do
    pattern fun (v_2418 : reg (bv 128)) (v_2419 : reg (bv 128)) (v_2420 : reg (bv 128)) => do
      v_4041 <- getRegister v_2420;
      v_4044 <- getRegister v_2418;
      v_4048 <- getRegister v_2419;
      setRegister (lhs.of_reg v_2420) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4041 0 64) 53 11) (MInt2Float (extract v_4044 0 64) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MInt2Float (extract v_4048 0 64) 53 11)) 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4041 64 128) 53 11) (MInt2Float (extract v_4044 64 128) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MInt2Float (extract v_4048 64 128) 53 11)) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2430 : reg (bv 256)) (v_2431 : reg (bv 256)) (v_2432 : reg (bv 256)) => do
      v_4075 <- getRegister v_2432;
      v_4077 <- getRegister v_2431;
      v_4079 <- getRegister v_2430;
      setRegister (lhs.of_reg v_2432) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4075 0 64) (extract v_4077 0 64) (extract v_4079 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4075 64 128) (extract v_4077 64 128) (extract v_4079 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4075 128 192) (extract v_4077 128 192) (extract v_4079 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4075 192 256) (extract v_4077 192 256) (extract v_4079 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2415 : Mem) (v_2413 : reg (bv 128)) (v_2414 : reg (bv 128)) => do
      v_10058 <- getRegister v_2414;
      v_10061 <- evaluateAddress v_2415;
      v_10062 <- load v_10061 16;
      v_10066 <- getRegister v_2413;
      setRegister (lhs.of_reg v_2414) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10058 0 64) 53 11) (MInt2Float (extract v_10062 0 64) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MInt2Float (extract v_10066 0 64) 53 11)) 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10058 64 128) 53 11) (MInt2Float (extract v_10062 64 128) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MInt2Float (extract v_10066 64 128) 53 11)) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2424 : Mem) (v_2425 : reg (bv 256)) (v_2426 : reg (bv 256)) => do
      v_10088 <- getRegister v_2426;
      v_10090 <- getRegister v_2425;
      v_10092 <- evaluateAddress v_2424;
      v_10093 <- load v_10092 32;
      setRegister (lhs.of_reg v_2426) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10088 0 64) (extract v_10090 0 64) (extract v_10093 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10088 64 128) (extract v_10090 64 128) (extract v_10093 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10088 128 192) (extract v_10090 128 192) (extract v_10093 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10088 192 256) (extract v_10090 192 256) (extract v_10093 192 256)))));
      pure ()
    pat_end
