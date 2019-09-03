def vfmadd132pd1 : instruction :=
  definst "vfmadd132pd" $ do
    pattern fun (v_2431 : reg (bv 128)) (v_2432 : reg (bv 128)) (v_2433 : reg (bv 128)) => do
      v_4053 <- getRegister v_2433;
      v_4054 <- eval (extract v_4053 0 64);
      v_4062 <- getRegister v_2431;
      v_4063 <- eval (extract v_4062 0 64);
      v_4072 <- getRegister v_2432;
      v_4073 <- eval (extract v_4072 0 64);
      v_4086 <- eval (extract v_4053 64 128);
      v_4094 <- eval (extract v_4062 64 128);
      v_4103 <- eval (extract v_4072 64 128);
      setRegister (lhs.of_reg v_2433) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4054 0 1)) (uvalueMInt (extract v_4054 1 12)) (uvalueMInt (extract v_4054 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4063 0 1)) (uvalueMInt (extract v_4063 1 12)) (uvalueMInt (extract v_4063 12 64)))) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4073 0 1)) (uvalueMInt (extract v_4073 1 12)) (uvalueMInt (extract v_4073 12 64)))) 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4086 0 1)) (uvalueMInt (extract v_4086 1 12)) (uvalueMInt (extract v_4086 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4094 0 1)) (uvalueMInt (extract v_4094 1 12)) (uvalueMInt (extract v_4094 12 64)))) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4103 0 1)) (uvalueMInt (extract v_4103 1 12)) (uvalueMInt (extract v_4103 12 64)))) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2442 : reg (bv 256)) (v_2443 : reg (bv 256)) (v_2444 : reg (bv 256)) => do
      v_4123 <- getRegister v_2444;
      v_4125 <- getRegister v_2443;
      v_4127 <- getRegister v_2442;
      setRegister (lhs.of_reg v_2444) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4123 0 64) (extract v_4125 0 64) (extract v_4127 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4123 64 128) (extract v_4125 64 128) (extract v_4127 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4123 128 192) (extract v_4125 128 192) (extract v_4127 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4123 192 256) (extract v_4125 192 256) (extract v_4127 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2428 : Mem) (v_2426 : reg (bv 128)) (v_2427 : reg (bv 128)) => do
      v_15002 <- getRegister v_2427;
      v_15003 <- eval (extract v_15002 0 64);
      v_15011 <- evaluateAddress v_2428;
      v_15012 <- load v_15011 16;
      v_15013 <- eval (extract v_15012 0 64);
      v_15022 <- getRegister v_2426;
      v_15023 <- eval (extract v_15022 0 64);
      v_15036 <- eval (extract v_15002 64 128);
      v_15044 <- eval (extract v_15012 64 128);
      v_15053 <- eval (extract v_15022 64 128);
      setRegister (lhs.of_reg v_2427) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_15003 0 1)) (uvalueMInt (extract v_15003 1 12)) (uvalueMInt (extract v_15003 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_15013 0 1)) (uvalueMInt (extract v_15013 1 12)) (uvalueMInt (extract v_15013 12 64)))) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MIntToFloatImpl 53 11 (uvalueMInt (extract v_15023 0 1)) (uvalueMInt (extract v_15023 1 12)) (uvalueMInt (extract v_15023 12 64)))) 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_15036 0 1)) (uvalueMInt (extract v_15036 1 12)) (uvalueMInt (extract v_15036 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_15044 0 1)) (uvalueMInt (extract v_15044 1 12)) (uvalueMInt (extract v_15044 12 64)))) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MIntToFloatImpl 53 11 (uvalueMInt (extract v_15053 0 1)) (uvalueMInt (extract v_15053 1 12)) (uvalueMInt (extract v_15053 12 64)))) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2437 : Mem) (v_2438 : reg (bv 256)) (v_2439 : reg (bv 256)) => do
      v_15068 <- getRegister v_2439;
      v_15070 <- getRegister v_2438;
      v_15072 <- evaluateAddress v_2437;
      v_15073 <- load v_15072 32;
      setRegister (lhs.of_reg v_2439) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_15068 0 64) (extract v_15070 0 64) (extract v_15073 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_15068 64 128) (extract v_15070 64 128) (extract v_15073 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_15068 128 192) (extract v_15070 128 192) (extract v_15073 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_15068 192 256) (extract v_15070 192 256) (extract v_15073 192 256)))));
      pure ()
    pat_end
