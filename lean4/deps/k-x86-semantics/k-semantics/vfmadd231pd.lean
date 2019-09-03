def vfmadd231pd1 : instruction :=
  definst "vfmadd231pd" $ do
    pattern fun (v_2563 : reg (bv 128)) (v_2564 : reg (bv 128)) (v_2565 : reg (bv 128)) => do
      v_5102 <- getRegister v_2564;
      v_5103 <- eval (extract v_5102 0 64);
      v_5111 <- getRegister v_2563;
      v_5112 <- eval (extract v_5111 0 64);
      v_5121 <- getRegister v_2565;
      v_5122 <- eval (extract v_5121 0 64);
      v_5135 <- eval (extract v_5102 64 128);
      v_5143 <- eval (extract v_5111 64 128);
      v_5152 <- eval (extract v_5121 64 128);
      setRegister (lhs.of_reg v_2565) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5103 0 1)) (uvalueMInt (extract v_5103 1 12)) (uvalueMInt (extract v_5103 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5112 0 1)) (uvalueMInt (extract v_5112 1 12)) (uvalueMInt (extract v_5112 12 64)))) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5122 0 1)) (uvalueMInt (extract v_5122 1 12)) (uvalueMInt (extract v_5122 12 64)))) 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5135 0 1)) (uvalueMInt (extract v_5135 1 12)) (uvalueMInt (extract v_5135 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5143 0 1)) (uvalueMInt (extract v_5143 1 12)) (uvalueMInt (extract v_5143 12 64)))) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5152 0 1)) (uvalueMInt (extract v_5152 1 12)) (uvalueMInt (extract v_5152 12 64)))) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2574 : reg (bv 256)) (v_2575 : reg (bv 256)) (v_2576 : reg (bv 256)) => do
      v_5172 <- getRegister v_2575;
      v_5174 <- getRegister v_2576;
      v_5176 <- getRegister v_2574;
      setRegister (lhs.of_reg v_2576) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_5172 0 64) (extract v_5174 0 64) (extract v_5176 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_5172 64 128) (extract v_5174 64 128) (extract v_5176 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_5172 128 192) (extract v_5174 128 192) (extract v_5176 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_5172 192 256) (extract v_5174 192 256) (extract v_5176 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2560 : Mem) (v_2558 : reg (bv 128)) (v_2559 : reg (bv 128)) => do
      v_15999 <- getRegister v_2558;
      v_16000 <- eval (extract v_15999 0 64);
      v_16008 <- evaluateAddress v_2560;
      v_16009 <- load v_16008 16;
      v_16010 <- eval (extract v_16009 0 64);
      v_16019 <- getRegister v_2559;
      v_16020 <- eval (extract v_16019 0 64);
      v_16033 <- eval (extract v_15999 64 128);
      v_16041 <- eval (extract v_16009 64 128);
      v_16050 <- eval (extract v_16019 64 128);
      setRegister (lhs.of_reg v_2559) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_16000 0 1)) (uvalueMInt (extract v_16000 1 12)) (uvalueMInt (extract v_16000 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_16010 0 1)) (uvalueMInt (extract v_16010 1 12)) (uvalueMInt (extract v_16010 12 64)))) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MIntToFloatImpl 53 11 (uvalueMInt (extract v_16020 0 1)) (uvalueMInt (extract v_16020 1 12)) (uvalueMInt (extract v_16020 12 64)))) 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_16033 0 1)) (uvalueMInt (extract v_16033 1 12)) (uvalueMInt (extract v_16033 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_16041 0 1)) (uvalueMInt (extract v_16041 1 12)) (uvalueMInt (extract v_16041 12 64)))) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MIntToFloatImpl 53 11 (uvalueMInt (extract v_16050 0 1)) (uvalueMInt (extract v_16050 1 12)) (uvalueMInt (extract v_16050 12 64)))) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2569 : Mem) (v_2570 : reg (bv 256)) (v_2571 : reg (bv 256)) => do
      v_16065 <- getRegister v_2570;
      v_16067 <- getRegister v_2571;
      v_16069 <- evaluateAddress v_2569;
      v_16070 <- load v_16069 32;
      setRegister (lhs.of_reg v_2571) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_16065 0 64) (extract v_16067 0 64) (extract v_16070 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_16065 64 128) (extract v_16067 64 128) (extract v_16070 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_16065 128 192) (extract v_16067 128 192) (extract v_16070 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_16065 192 256) (extract v_16067 192 256) (extract v_16070 192 256)))));
      pure ()
    pat_end
