def vhaddps1 : instruction :=
  definst "vhaddps" $ do
    pattern fun (v_2398 : reg (bv 128)) (v_2399 : reg (bv 128)) (v_2400 : reg (bv 128)) => do
      v_3944 <- getRegister v_2398;
      v_3945 <- eval (extract v_3944 32 64);
      v_3953 <- eval (extract v_3944 0 32);
      v_3963 <- eval (extract v_3944 96 128);
      v_3971 <- eval (extract v_3944 64 96);
      v_3982 <- getRegister v_2399;
      v_3983 <- eval (extract v_3982 32 64);
      v_3991 <- eval (extract v_3982 0 32);
      v_4002 <- eval (extract v_3982 96 128);
      v_4010 <- eval (extract v_3982 64 96);
      setRegister (lhs.of_reg v_2400) (concat (concat (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_3945 0 1)) (uvalueMInt (extract v_3945 1 9)) (uvalueMInt (extract v_3945 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_3953 0 1)) (uvalueMInt (extract v_3953 1 9)) (uvalueMInt (extract v_3953 9 32)))) 32) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_3963 0 1)) (uvalueMInt (extract v_3963 1 9)) (uvalueMInt (extract v_3963 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_3971 0 1)) (uvalueMInt (extract v_3971 1 9)) (uvalueMInt (extract v_3971 9 32)))) 32)) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_3983 0 1)) (uvalueMInt (extract v_3983 1 9)) (uvalueMInt (extract v_3983 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_3991 0 1)) (uvalueMInt (extract v_3991 1 9)) (uvalueMInt (extract v_3991 9 32)))) 32)) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4002 0 1)) (uvalueMInt (extract v_4002 1 9)) (uvalueMInt (extract v_4002 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4010 0 1)) (uvalueMInt (extract v_4010 1 9)) (uvalueMInt (extract v_4010 9 32)))) 32));
      pure ()
    pat_end;
    pattern fun (v_2409 : reg (bv 256)) (v_2410 : reg (bv 256)) (v_2411 : reg (bv 256)) => do
      v_4027 <- getRegister v_2409;
      v_4028 <- eval (extract v_4027 32 64);
      v_4036 <- eval (extract v_4027 0 32);
      v_4046 <- eval (extract v_4027 96 128);
      v_4054 <- eval (extract v_4027 64 96);
      v_4065 <- getRegister v_2410;
      v_4066 <- eval (extract v_4065 32 64);
      v_4074 <- eval (extract v_4065 0 32);
      v_4085 <- eval (extract v_4065 96 128);
      v_4093 <- eval (extract v_4065 64 96);
      v_4104 <- eval (extract v_4027 160 192);
      v_4112 <- eval (extract v_4027 128 160);
      v_4122 <- eval (extract v_4027 224 256);
      v_4130 <- eval (extract v_4027 192 224);
      v_4141 <- eval (extract v_4065 160 192);
      v_4149 <- eval (extract v_4065 128 160);
      v_4160 <- eval (extract v_4065 224 256);
      v_4168 <- eval (extract v_4065 192 224);
      setRegister (lhs.of_reg v_2411) (concat (concat (concat (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4028 0 1)) (uvalueMInt (extract v_4028 1 9)) (uvalueMInt (extract v_4028 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4036 0 1)) (uvalueMInt (extract v_4036 1 9)) (uvalueMInt (extract v_4036 9 32)))) 32) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4046 0 1)) (uvalueMInt (extract v_4046 1 9)) (uvalueMInt (extract v_4046 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4054 0 1)) (uvalueMInt (extract v_4054 1 9)) (uvalueMInt (extract v_4054 9 32)))) 32)) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4066 0 1)) (uvalueMInt (extract v_4066 1 9)) (uvalueMInt (extract v_4066 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4074 0 1)) (uvalueMInt (extract v_4074 1 9)) (uvalueMInt (extract v_4074 9 32)))) 32)) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4085 0 1)) (uvalueMInt (extract v_4085 1 9)) (uvalueMInt (extract v_4085 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4093 0 1)) (uvalueMInt (extract v_4093 1 9)) (uvalueMInt (extract v_4093 9 32)))) 32)) (concat (concat (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4104 0 1)) (uvalueMInt (extract v_4104 1 9)) (uvalueMInt (extract v_4104 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4112 0 1)) (uvalueMInt (extract v_4112 1 9)) (uvalueMInt (extract v_4112 9 32)))) 32) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4122 0 1)) (uvalueMInt (extract v_4122 1 9)) (uvalueMInt (extract v_4122 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4130 0 1)) (uvalueMInt (extract v_4130 1 9)) (uvalueMInt (extract v_4130 9 32)))) 32)) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4141 0 1)) (uvalueMInt (extract v_4141 1 9)) (uvalueMInt (extract v_4141 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4149 0 1)) (uvalueMInt (extract v_4149 1 9)) (uvalueMInt (extract v_4149 9 32)))) 32)) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4160 0 1)) (uvalueMInt (extract v_4160 1 9)) (uvalueMInt (extract v_4160 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4168 0 1)) (uvalueMInt (extract v_4168 1 9)) (uvalueMInt (extract v_4168 9 32)))) 32)));
      pure ()
    pat_end;
    pattern fun (v_2393 : Mem) (v_2394 : reg (bv 128)) (v_2395 : reg (bv 128)) => do
      v_10022 <- evaluateAddress v_2393;
      v_10023 <- load v_10022 16;
      v_10024 <- eval (extract v_10023 32 64);
      v_10032 <- eval (extract v_10023 0 32);
      v_10042 <- eval (extract v_10023 96 128);
      v_10050 <- eval (extract v_10023 64 96);
      v_10061 <- getRegister v_2394;
      v_10062 <- eval (extract v_10061 32 64);
      v_10070 <- eval (extract v_10061 0 32);
      v_10081 <- eval (extract v_10061 96 128);
      v_10089 <- eval (extract v_10061 64 96);
      setRegister (lhs.of_reg v_2395) (concat (concat (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10024 0 1)) (uvalueMInt (extract v_10024 1 9)) (uvalueMInt (extract v_10024 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10032 0 1)) (uvalueMInt (extract v_10032 1 9)) (uvalueMInt (extract v_10032 9 32)))) 32) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10042 0 1)) (uvalueMInt (extract v_10042 1 9)) (uvalueMInt (extract v_10042 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10050 0 1)) (uvalueMInt (extract v_10050 1 9)) (uvalueMInt (extract v_10050 9 32)))) 32)) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10062 0 1)) (uvalueMInt (extract v_10062 1 9)) (uvalueMInt (extract v_10062 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10070 0 1)) (uvalueMInt (extract v_10070 1 9)) (uvalueMInt (extract v_10070 9 32)))) 32)) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10081 0 1)) (uvalueMInt (extract v_10081 1 9)) (uvalueMInt (extract v_10081 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10089 0 1)) (uvalueMInt (extract v_10089 1 9)) (uvalueMInt (extract v_10089 9 32)))) 32));
      pure ()
    pat_end;
    pattern fun (v_2404 : Mem) (v_2405 : reg (bv 256)) (v_2406 : reg (bv 256)) => do
      v_10101 <- evaluateAddress v_2404;
      v_10102 <- load v_10101 32;
      v_10103 <- eval (extract v_10102 32 64);
      v_10111 <- eval (extract v_10102 0 32);
      v_10121 <- eval (extract v_10102 96 128);
      v_10129 <- eval (extract v_10102 64 96);
      v_10140 <- getRegister v_2405;
      v_10141 <- eval (extract v_10140 32 64);
      v_10149 <- eval (extract v_10140 0 32);
      v_10160 <- eval (extract v_10140 96 128);
      v_10168 <- eval (extract v_10140 64 96);
      v_10179 <- eval (extract v_10102 160 192);
      v_10187 <- eval (extract v_10102 128 160);
      v_10197 <- eval (extract v_10102 224 256);
      v_10205 <- eval (extract v_10102 192 224);
      v_10216 <- eval (extract v_10140 160 192);
      v_10224 <- eval (extract v_10140 128 160);
      v_10235 <- eval (extract v_10140 224 256);
      v_10243 <- eval (extract v_10140 192 224);
      setRegister (lhs.of_reg v_2406) (concat (concat (concat (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10103 0 1)) (uvalueMInt (extract v_10103 1 9)) (uvalueMInt (extract v_10103 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10111 0 1)) (uvalueMInt (extract v_10111 1 9)) (uvalueMInt (extract v_10111 9 32)))) 32) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10121 0 1)) (uvalueMInt (extract v_10121 1 9)) (uvalueMInt (extract v_10121 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10129 0 1)) (uvalueMInt (extract v_10129 1 9)) (uvalueMInt (extract v_10129 9 32)))) 32)) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10141 0 1)) (uvalueMInt (extract v_10141 1 9)) (uvalueMInt (extract v_10141 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10149 0 1)) (uvalueMInt (extract v_10149 1 9)) (uvalueMInt (extract v_10149 9 32)))) 32)) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10160 0 1)) (uvalueMInt (extract v_10160 1 9)) (uvalueMInt (extract v_10160 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10168 0 1)) (uvalueMInt (extract v_10168 1 9)) (uvalueMInt (extract v_10168 9 32)))) 32)) (concat (concat (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10179 0 1)) (uvalueMInt (extract v_10179 1 9)) (uvalueMInt (extract v_10179 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10187 0 1)) (uvalueMInt (extract v_10187 1 9)) (uvalueMInt (extract v_10187 9 32)))) 32) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10197 0 1)) (uvalueMInt (extract v_10197 1 9)) (uvalueMInt (extract v_10197 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10205 0 1)) (uvalueMInt (extract v_10205 1 9)) (uvalueMInt (extract v_10205 9 32)))) 32)) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10216 0 1)) (uvalueMInt (extract v_10216 1 9)) (uvalueMInt (extract v_10216 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10224 0 1)) (uvalueMInt (extract v_10224 1 9)) (uvalueMInt (extract v_10224 9 32)))) 32)) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10235 0 1)) (uvalueMInt (extract v_10235 1 9)) (uvalueMInt (extract v_10235 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10243 0 1)) (uvalueMInt (extract v_10243 1 9)) (uvalueMInt (extract v_10243 9 32)))) 32)));
      pure ()
    pat_end
