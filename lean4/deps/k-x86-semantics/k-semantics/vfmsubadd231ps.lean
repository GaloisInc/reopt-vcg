def vfmsubadd231ps1 : instruction :=
  definst "vfmsubadd231ps" $ do
    pattern fun (v_3069 : reg (bv 128)) (v_3070 : reg (bv 128)) (v_3071 : reg (bv 128)) => do
      v_10196 <- getRegister v_3070;
      v_10197 <- eval (extract v_10196 0 32);
      v_10205 <- getRegister v_3069;
      v_10206 <- eval (extract v_10205 0 32);
      v_10215 <- getRegister v_3071;
      v_10216 <- eval (extract v_10215 0 32);
      v_10226 <- eval (extract v_10196 32 64);
      v_10234 <- eval (extract v_10205 32 64);
      v_10243 <- eval (extract v_10215 32 64);
      v_10254 <- eval (extract v_10196 64 96);
      v_10262 <- eval (extract v_10205 64 96);
      v_10271 <- eval (extract v_10215 64 96);
      v_10281 <- eval (extract v_10196 96 128);
      v_10289 <- eval (extract v_10205 96 128);
      v_10298 <- eval (extract v_10215 96 128);
      setRegister (lhs.of_reg v_3071) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10197 0 1)) (uvalueMInt (extract v_10197 1 9)) (uvalueMInt (extract v_10197 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10206 0 1)) (uvalueMInt (extract v_10206 1 9)) (uvalueMInt (extract v_10206 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10216 0 1)) (uvalueMInt (extract v_10216 1 9)) (uvalueMInt (extract v_10216 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10226 0 1)) (uvalueMInt (extract v_10226 1 9)) (uvalueMInt (extract v_10226 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10234 0 1)) (uvalueMInt (extract v_10234 1 9)) (uvalueMInt (extract v_10234 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10243 0 1)) (uvalueMInt (extract v_10243 1 9)) (uvalueMInt (extract v_10243 9 32)))) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10254 0 1)) (uvalueMInt (extract v_10254 1 9)) (uvalueMInt (extract v_10254 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10262 0 1)) (uvalueMInt (extract v_10262 1 9)) (uvalueMInt (extract v_10262 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10271 0 1)) (uvalueMInt (extract v_10271 1 9)) (uvalueMInt (extract v_10271 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10281 0 1)) (uvalueMInt (extract v_10281 1 9)) (uvalueMInt (extract v_10281 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10289 0 1)) (uvalueMInt (extract v_10289 1 9)) (uvalueMInt (extract v_10289 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10298 0 1)) (uvalueMInt (extract v_10298 1 9)) (uvalueMInt (extract v_10298 9 32)))) 32)));
      pure ()
    pat_end;
    pattern fun (v_3080 : reg (bv 256)) (v_3081 : reg (bv 256)) (v_3082 : reg (bv 256)) => do
      v_10316 <- getRegister v_3081;
      v_10317 <- eval (extract v_10316 0 32);
      v_10325 <- getRegister v_3080;
      v_10326 <- eval (extract v_10325 0 32);
      v_10335 <- getRegister v_3082;
      v_10336 <- eval (extract v_10335 0 32);
      v_10346 <- eval (extract v_10316 32 64);
      v_10354 <- eval (extract v_10325 32 64);
      v_10363 <- eval (extract v_10335 32 64);
      v_10374 <- eval (extract v_10316 64 96);
      v_10382 <- eval (extract v_10325 64 96);
      v_10391 <- eval (extract v_10335 64 96);
      v_10401 <- eval (extract v_10316 96 128);
      v_10409 <- eval (extract v_10325 96 128);
      v_10418 <- eval (extract v_10335 96 128);
      v_10429 <- eval (extract v_10316 128 160);
      v_10437 <- eval (extract v_10325 128 160);
      v_10446 <- eval (extract v_10335 128 160);
      v_10456 <- eval (extract v_10316 160 192);
      v_10464 <- eval (extract v_10325 160 192);
      v_10473 <- eval (extract v_10335 160 192);
      v_10484 <- eval (extract v_10316 192 224);
      v_10492 <- eval (extract v_10325 192 224);
      v_10501 <- eval (extract v_10335 192 224);
      v_10511 <- eval (extract v_10316 224 256);
      v_10519 <- eval (extract v_10325 224 256);
      v_10528 <- eval (extract v_10335 224 256);
      setRegister (lhs.of_reg v_3082) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10317 0 1)) (uvalueMInt (extract v_10317 1 9)) (uvalueMInt (extract v_10317 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10326 0 1)) (uvalueMInt (extract v_10326 1 9)) (uvalueMInt (extract v_10326 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10336 0 1)) (uvalueMInt (extract v_10336 1 9)) (uvalueMInt (extract v_10336 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10346 0 1)) (uvalueMInt (extract v_10346 1 9)) (uvalueMInt (extract v_10346 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10354 0 1)) (uvalueMInt (extract v_10354 1 9)) (uvalueMInt (extract v_10354 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10363 0 1)) (uvalueMInt (extract v_10363 1 9)) (uvalueMInt (extract v_10363 9 32)))) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10374 0 1)) (uvalueMInt (extract v_10374 1 9)) (uvalueMInt (extract v_10374 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10382 0 1)) (uvalueMInt (extract v_10382 1 9)) (uvalueMInt (extract v_10382 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10391 0 1)) (uvalueMInt (extract v_10391 1 9)) (uvalueMInt (extract v_10391 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10401 0 1)) (uvalueMInt (extract v_10401 1 9)) (uvalueMInt (extract v_10401 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10409 0 1)) (uvalueMInt (extract v_10409 1 9)) (uvalueMInt (extract v_10409 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10418 0 1)) (uvalueMInt (extract v_10418 1 9)) (uvalueMInt (extract v_10418 9 32)))) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10429 0 1)) (uvalueMInt (extract v_10429 1 9)) (uvalueMInt (extract v_10429 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10437 0 1)) (uvalueMInt (extract v_10437 1 9)) (uvalueMInt (extract v_10437 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10446 0 1)) (uvalueMInt (extract v_10446 1 9)) (uvalueMInt (extract v_10446 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10456 0 1)) (uvalueMInt (extract v_10456 1 9)) (uvalueMInt (extract v_10456 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10464 0 1)) (uvalueMInt (extract v_10464 1 9)) (uvalueMInt (extract v_10464 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10473 0 1)) (uvalueMInt (extract v_10473 1 9)) (uvalueMInt (extract v_10473 9 32)))) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10484 0 1)) (uvalueMInt (extract v_10484 1 9)) (uvalueMInt (extract v_10484 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10492 0 1)) (uvalueMInt (extract v_10492 1 9)) (uvalueMInt (extract v_10492 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10501 0 1)) (uvalueMInt (extract v_10501 1 9)) (uvalueMInt (extract v_10501 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10511 0 1)) (uvalueMInt (extract v_10511 1 9)) (uvalueMInt (extract v_10511 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10519 0 1)) (uvalueMInt (extract v_10519 1 9)) (uvalueMInt (extract v_10519 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10528 0 1)) (uvalueMInt (extract v_10528 1 9)) (uvalueMInt (extract v_10528 9 32)))) 32)))));
      pure ()
    pat_end;
    pattern fun (v_3066 : Mem) (v_3064 : reg (bv 128)) (v_3065 : reg (bv 128)) => do
      v_20901 <- getRegister v_3064;
      v_20902 <- eval (extract v_20901 0 32);
      v_20910 <- evaluateAddress v_3066;
      v_20911 <- load v_20910 16;
      v_20912 <- eval (extract v_20911 0 32);
      v_20921 <- getRegister v_3065;
      v_20922 <- eval (extract v_20921 0 32);
      v_20932 <- eval (extract v_20901 32 64);
      v_20940 <- eval (extract v_20911 32 64);
      v_20949 <- eval (extract v_20921 32 64);
      v_20960 <- eval (extract v_20901 64 96);
      v_20968 <- eval (extract v_20911 64 96);
      v_20977 <- eval (extract v_20921 64 96);
      v_20987 <- eval (extract v_20901 96 128);
      v_20995 <- eval (extract v_20911 96 128);
      v_21004 <- eval (extract v_20921 96 128);
      setRegister (lhs.of_reg v_3065) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20902 0 1)) (uvalueMInt (extract v_20902 1 9)) (uvalueMInt (extract v_20902 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20912 0 1)) (uvalueMInt (extract v_20912 1 9)) (uvalueMInt (extract v_20912 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20922 0 1)) (uvalueMInt (extract v_20922 1 9)) (uvalueMInt (extract v_20922 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20932 0 1)) (uvalueMInt (extract v_20932 1 9)) (uvalueMInt (extract v_20932 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20940 0 1)) (uvalueMInt (extract v_20940 1 9)) (uvalueMInt (extract v_20940 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20949 0 1)) (uvalueMInt (extract v_20949 1 9)) (uvalueMInt (extract v_20949 9 32)))) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20960 0 1)) (uvalueMInt (extract v_20960 1 9)) (uvalueMInt (extract v_20960 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20968 0 1)) (uvalueMInt (extract v_20968 1 9)) (uvalueMInt (extract v_20968 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20977 0 1)) (uvalueMInt (extract v_20977 1 9)) (uvalueMInt (extract v_20977 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20987 0 1)) (uvalueMInt (extract v_20987 1 9)) (uvalueMInt (extract v_20987 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20995 0 1)) (uvalueMInt (extract v_20995 1 9)) (uvalueMInt (extract v_20995 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21004 0 1)) (uvalueMInt (extract v_21004 1 9)) (uvalueMInt (extract v_21004 9 32)))) 32)));
      pure ()
    pat_end;
    pattern fun (v_3075 : Mem) (v_3076 : reg (bv 256)) (v_3077 : reg (bv 256)) => do
      v_21017 <- getRegister v_3076;
      v_21018 <- eval (extract v_21017 0 32);
      v_21026 <- evaluateAddress v_3075;
      v_21027 <- load v_21026 32;
      v_21028 <- eval (extract v_21027 0 32);
      v_21037 <- getRegister v_3077;
      v_21038 <- eval (extract v_21037 0 32);
      v_21048 <- eval (extract v_21017 32 64);
      v_21056 <- eval (extract v_21027 32 64);
      v_21065 <- eval (extract v_21037 32 64);
      v_21076 <- eval (extract v_21017 64 96);
      v_21084 <- eval (extract v_21027 64 96);
      v_21093 <- eval (extract v_21037 64 96);
      v_21103 <- eval (extract v_21017 96 128);
      v_21111 <- eval (extract v_21027 96 128);
      v_21120 <- eval (extract v_21037 96 128);
      v_21131 <- eval (extract v_21017 128 160);
      v_21139 <- eval (extract v_21027 128 160);
      v_21148 <- eval (extract v_21037 128 160);
      v_21158 <- eval (extract v_21017 160 192);
      v_21166 <- eval (extract v_21027 160 192);
      v_21175 <- eval (extract v_21037 160 192);
      v_21186 <- eval (extract v_21017 192 224);
      v_21194 <- eval (extract v_21027 192 224);
      v_21203 <- eval (extract v_21037 192 224);
      v_21213 <- eval (extract v_21017 224 256);
      v_21221 <- eval (extract v_21027 224 256);
      v_21230 <- eval (extract v_21037 224 256);
      setRegister (lhs.of_reg v_3077) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21018 0 1)) (uvalueMInt (extract v_21018 1 9)) (uvalueMInt (extract v_21018 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21028 0 1)) (uvalueMInt (extract v_21028 1 9)) (uvalueMInt (extract v_21028 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21038 0 1)) (uvalueMInt (extract v_21038 1 9)) (uvalueMInt (extract v_21038 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21048 0 1)) (uvalueMInt (extract v_21048 1 9)) (uvalueMInt (extract v_21048 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21056 0 1)) (uvalueMInt (extract v_21056 1 9)) (uvalueMInt (extract v_21056 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21065 0 1)) (uvalueMInt (extract v_21065 1 9)) (uvalueMInt (extract v_21065 9 32)))) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21076 0 1)) (uvalueMInt (extract v_21076 1 9)) (uvalueMInt (extract v_21076 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21084 0 1)) (uvalueMInt (extract v_21084 1 9)) (uvalueMInt (extract v_21084 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21093 0 1)) (uvalueMInt (extract v_21093 1 9)) (uvalueMInt (extract v_21093 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21103 0 1)) (uvalueMInt (extract v_21103 1 9)) (uvalueMInt (extract v_21103 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21111 0 1)) (uvalueMInt (extract v_21111 1 9)) (uvalueMInt (extract v_21111 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21120 0 1)) (uvalueMInt (extract v_21120 1 9)) (uvalueMInt (extract v_21120 9 32)))) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21131 0 1)) (uvalueMInt (extract v_21131 1 9)) (uvalueMInt (extract v_21131 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21139 0 1)) (uvalueMInt (extract v_21139 1 9)) (uvalueMInt (extract v_21139 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21148 0 1)) (uvalueMInt (extract v_21148 1 9)) (uvalueMInt (extract v_21148 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21158 0 1)) (uvalueMInt (extract v_21158 1 9)) (uvalueMInt (extract v_21158 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21166 0 1)) (uvalueMInt (extract v_21166 1 9)) (uvalueMInt (extract v_21166 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21175 0 1)) (uvalueMInt (extract v_21175 1 9)) (uvalueMInt (extract v_21175 9 32)))) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21186 0 1)) (uvalueMInt (extract v_21186 1 9)) (uvalueMInt (extract v_21186 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21194 0 1)) (uvalueMInt (extract v_21194 1 9)) (uvalueMInt (extract v_21194 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21203 0 1)) (uvalueMInt (extract v_21203 1 9)) (uvalueMInt (extract v_21203 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21213 0 1)) (uvalueMInt (extract v_21213 1 9)) (uvalueMInt (extract v_21213 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21221 0 1)) (uvalueMInt (extract v_21221 1 9)) (uvalueMInt (extract v_21221 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21230 0 1)) (uvalueMInt (extract v_21230 1 9)) (uvalueMInt (extract v_21230 9 32)))) 32)))));
      pure ()
    pat_end
