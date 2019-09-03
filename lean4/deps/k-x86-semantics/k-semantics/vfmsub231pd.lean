def vfmsub231pd1 : instruction :=
  definst "vfmsub231pd" $ do
    pattern fun (v_2893 : reg (bv 128)) (v_2894 : reg (bv 128)) (v_2895 : reg (bv 128)) => do
      v_8397 <- getRegister v_2894;
      v_8398 <- eval (extract v_8397 0 64);
      v_8406 <- getRegister v_2893;
      v_8407 <- eval (extract v_8406 0 64);
      v_8416 <- getRegister v_2895;
      v_8417 <- eval (extract v_8416 0 64);
      v_8427 <- eval (extract v_8397 64 128);
      v_8435 <- eval (extract v_8406 64 128);
      v_8444 <- eval (extract v_8416 64 128);
      setRegister (lhs.of_reg v_2895) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8398 0 1)) (uvalueMInt (extract v_8398 1 12)) (uvalueMInt (extract v_8398 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8407 0 1)) (uvalueMInt (extract v_8407 1 12)) (uvalueMInt (extract v_8407 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8417 0 1)) (uvalueMInt (extract v_8417 1 12)) (uvalueMInt (extract v_8417 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8427 0 1)) (uvalueMInt (extract v_8427 1 12)) (uvalueMInt (extract v_8427 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8435 0 1)) (uvalueMInt (extract v_8435 1 12)) (uvalueMInt (extract v_8435 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8444 0 1)) (uvalueMInt (extract v_8444 1 12)) (uvalueMInt (extract v_8444 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2904 : reg (bv 256)) (v_2905 : reg (bv 256)) (v_2906 : reg (bv 256)) => do
      v_8461 <- getRegister v_2905;
      v_8462 <- eval (extract v_8461 0 64);
      v_8470 <- getRegister v_2904;
      v_8471 <- eval (extract v_8470 0 64);
      v_8480 <- getRegister v_2906;
      v_8481 <- eval (extract v_8480 0 64);
      v_8491 <- eval (extract v_8461 64 128);
      v_8499 <- eval (extract v_8470 64 128);
      v_8508 <- eval (extract v_8480 64 128);
      v_8519 <- eval (extract v_8461 128 192);
      v_8527 <- eval (extract v_8470 128 192);
      v_8536 <- eval (extract v_8480 128 192);
      v_8546 <- eval (extract v_8461 192 256);
      v_8554 <- eval (extract v_8470 192 256);
      v_8563 <- eval (extract v_8480 192 256);
      setRegister (lhs.of_reg v_2906) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8462 0 1)) (uvalueMInt (extract v_8462 1 12)) (uvalueMInt (extract v_8462 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8471 0 1)) (uvalueMInt (extract v_8471 1 12)) (uvalueMInt (extract v_8471 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8481 0 1)) (uvalueMInt (extract v_8481 1 12)) (uvalueMInt (extract v_8481 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8491 0 1)) (uvalueMInt (extract v_8491 1 12)) (uvalueMInt (extract v_8491 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8499 0 1)) (uvalueMInt (extract v_8499 1 12)) (uvalueMInt (extract v_8499 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8508 0 1)) (uvalueMInt (extract v_8508 1 12)) (uvalueMInt (extract v_8508 12 64)))) 64)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8519 0 1)) (uvalueMInt (extract v_8519 1 12)) (uvalueMInt (extract v_8519 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8527 0 1)) (uvalueMInt (extract v_8527 1 12)) (uvalueMInt (extract v_8527 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8536 0 1)) (uvalueMInt (extract v_8536 1 12)) (uvalueMInt (extract v_8536 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8546 0 1)) (uvalueMInt (extract v_8546 1 12)) (uvalueMInt (extract v_8546 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8554 0 1)) (uvalueMInt (extract v_8554 1 12)) (uvalueMInt (extract v_8554 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8563 0 1)) (uvalueMInt (extract v_8563 1 12)) (uvalueMInt (extract v_8563 12 64)))) 64)));
      pure ()
    pat_end;
    pattern fun (v_2890 : Mem) (v_2888 : reg (bv 128)) (v_2889 : reg (bv 128)) => do
      v_19168 <- getRegister v_2888;
      v_19169 <- eval (extract v_19168 0 64);
      v_19177 <- evaluateAddress v_2890;
      v_19178 <- load v_19177 16;
      v_19179 <- eval (extract v_19178 0 64);
      v_19188 <- getRegister v_2889;
      v_19189 <- eval (extract v_19188 0 64);
      v_19199 <- eval (extract v_19168 64 128);
      v_19207 <- eval (extract v_19178 64 128);
      v_19216 <- eval (extract v_19188 64 128);
      setRegister (lhs.of_reg v_2889) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19169 0 1)) (uvalueMInt (extract v_19169 1 12)) (uvalueMInt (extract v_19169 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19179 0 1)) (uvalueMInt (extract v_19179 1 12)) (uvalueMInt (extract v_19179 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19189 0 1)) (uvalueMInt (extract v_19189 1 12)) (uvalueMInt (extract v_19189 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19199 0 1)) (uvalueMInt (extract v_19199 1 12)) (uvalueMInt (extract v_19199 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19207 0 1)) (uvalueMInt (extract v_19207 1 12)) (uvalueMInt (extract v_19207 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19216 0 1)) (uvalueMInt (extract v_19216 1 12)) (uvalueMInt (extract v_19216 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2899 : Mem) (v_2900 : reg (bv 256)) (v_2901 : reg (bv 256)) => do
      v_19228 <- getRegister v_2900;
      v_19229 <- eval (extract v_19228 0 64);
      v_19237 <- evaluateAddress v_2899;
      v_19238 <- load v_19237 32;
      v_19239 <- eval (extract v_19238 0 64);
      v_19248 <- getRegister v_2901;
      v_19249 <- eval (extract v_19248 0 64);
      v_19259 <- eval (extract v_19228 64 128);
      v_19267 <- eval (extract v_19238 64 128);
      v_19276 <- eval (extract v_19248 64 128);
      v_19287 <- eval (extract v_19228 128 192);
      v_19295 <- eval (extract v_19238 128 192);
      v_19304 <- eval (extract v_19248 128 192);
      v_19314 <- eval (extract v_19228 192 256);
      v_19322 <- eval (extract v_19238 192 256);
      v_19331 <- eval (extract v_19248 192 256);
      setRegister (lhs.of_reg v_2901) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19229 0 1)) (uvalueMInt (extract v_19229 1 12)) (uvalueMInt (extract v_19229 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19239 0 1)) (uvalueMInt (extract v_19239 1 12)) (uvalueMInt (extract v_19239 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19249 0 1)) (uvalueMInt (extract v_19249 1 12)) (uvalueMInt (extract v_19249 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19259 0 1)) (uvalueMInt (extract v_19259 1 12)) (uvalueMInt (extract v_19259 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19267 0 1)) (uvalueMInt (extract v_19267 1 12)) (uvalueMInt (extract v_19267 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19276 0 1)) (uvalueMInt (extract v_19276 1 12)) (uvalueMInt (extract v_19276 12 64)))) 64)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19287 0 1)) (uvalueMInt (extract v_19287 1 12)) (uvalueMInt (extract v_19287 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19295 0 1)) (uvalueMInt (extract v_19295 1 12)) (uvalueMInt (extract v_19295 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19304 0 1)) (uvalueMInt (extract v_19304 1 12)) (uvalueMInt (extract v_19304 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19314 0 1)) (uvalueMInt (extract v_19314 1 12)) (uvalueMInt (extract v_19314 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19322 0 1)) (uvalueMInt (extract v_19322 1 12)) (uvalueMInt (extract v_19322 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19331 0 1)) (uvalueMInt (extract v_19331 1 12)) (uvalueMInt (extract v_19331 12 64)))) 64)));
      pure ()
    pat_end
