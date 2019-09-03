def vfnmsub132ps1 : instruction :=
  definst "vfnmsub132ps" $ do
    pattern fun (v_3311 : reg (bv 128)) (v_3312 : reg (bv 128)) (v_3313 : reg (bv 128)) => do
      v_11223 <- getRegister v_3313;
      v_11224 <- eval (extract v_11223 0 32);
      v_11232 <- getRegister v_3311;
      v_11233 <- eval (extract v_11232 0 32);
      v_11243 <- getRegister v_3312;
      v_11244 <- eval (extract v_11243 0 32);
      v_11254 <- eval (extract v_11223 32 64);
      v_11262 <- eval (extract v_11232 32 64);
      v_11272 <- eval (extract v_11243 32 64);
      v_11282 <- eval (extract v_11223 64 96);
      v_11290 <- eval (extract v_11232 64 96);
      v_11300 <- eval (extract v_11243 64 96);
      v_11310 <- eval (extract v_11223 96 128);
      v_11318 <- eval (extract v_11232 96 128);
      v_11328 <- eval (extract v_11243 96 128);
      setRegister (lhs.of_reg v_3313) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11224 0 1)) (uvalueMInt (extract v_11224 1 9)) (uvalueMInt (extract v_11224 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11233 0 1)) (uvalueMInt (extract v_11233 1 9)) (uvalueMInt (extract v_11233 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11244 0 1)) (uvalueMInt (extract v_11244 1 9)) (uvalueMInt (extract v_11244 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11254 0 1)) (uvalueMInt (extract v_11254 1 9)) (uvalueMInt (extract v_11254 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11262 0 1)) (uvalueMInt (extract v_11262 1 9)) (uvalueMInt (extract v_11262 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11272 0 1)) (uvalueMInt (extract v_11272 1 9)) (uvalueMInt (extract v_11272 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11282 0 1)) (uvalueMInt (extract v_11282 1 9)) (uvalueMInt (extract v_11282 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11290 0 1)) (uvalueMInt (extract v_11290 1 9)) (uvalueMInt (extract v_11290 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11300 0 1)) (uvalueMInt (extract v_11300 1 9)) (uvalueMInt (extract v_11300 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11310 0 1)) (uvalueMInt (extract v_11310 1 9)) (uvalueMInt (extract v_11310 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11318 0 1)) (uvalueMInt (extract v_11318 1 9)) (uvalueMInt (extract v_11318 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11328 0 1)) (uvalueMInt (extract v_11328 1 9)) (uvalueMInt (extract v_11328 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_3322 : reg (bv 256)) (v_3323 : reg (bv 256)) (v_3324 : reg (bv 256)) => do
      v_11347 <- getRegister v_3324;
      v_11348 <- eval (extract v_11347 0 32);
      v_11356 <- getRegister v_3322;
      v_11357 <- eval (extract v_11356 0 32);
      v_11367 <- getRegister v_3323;
      v_11368 <- eval (extract v_11367 0 32);
      v_11378 <- eval (extract v_11347 32 64);
      v_11386 <- eval (extract v_11356 32 64);
      v_11396 <- eval (extract v_11367 32 64);
      v_11406 <- eval (extract v_11347 64 96);
      v_11414 <- eval (extract v_11356 64 96);
      v_11424 <- eval (extract v_11367 64 96);
      v_11434 <- eval (extract v_11347 96 128);
      v_11442 <- eval (extract v_11356 96 128);
      v_11452 <- eval (extract v_11367 96 128);
      v_11462 <- eval (extract v_11347 128 160);
      v_11470 <- eval (extract v_11356 128 160);
      v_11480 <- eval (extract v_11367 128 160);
      v_11490 <- eval (extract v_11347 160 192);
      v_11498 <- eval (extract v_11356 160 192);
      v_11508 <- eval (extract v_11367 160 192);
      v_11518 <- eval (extract v_11347 192 224);
      v_11526 <- eval (extract v_11356 192 224);
      v_11536 <- eval (extract v_11367 192 224);
      v_11546 <- eval (extract v_11347 224 256);
      v_11554 <- eval (extract v_11356 224 256);
      v_11564 <- eval (extract v_11367 224 256);
      setRegister (lhs.of_reg v_3324) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11348 0 1)) (uvalueMInt (extract v_11348 1 9)) (uvalueMInt (extract v_11348 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11357 0 1)) (uvalueMInt (extract v_11357 1 9)) (uvalueMInt (extract v_11357 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11368 0 1)) (uvalueMInt (extract v_11368 1 9)) (uvalueMInt (extract v_11368 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11378 0 1)) (uvalueMInt (extract v_11378 1 9)) (uvalueMInt (extract v_11378 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11386 0 1)) (uvalueMInt (extract v_11386 1 9)) (uvalueMInt (extract v_11386 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11396 0 1)) (uvalueMInt (extract v_11396 1 9)) (uvalueMInt (extract v_11396 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11406 0 1)) (uvalueMInt (extract v_11406 1 9)) (uvalueMInt (extract v_11406 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11414 0 1)) (uvalueMInt (extract v_11414 1 9)) (uvalueMInt (extract v_11414 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11424 0 1)) (uvalueMInt (extract v_11424 1 9)) (uvalueMInt (extract v_11424 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11434 0 1)) (uvalueMInt (extract v_11434 1 9)) (uvalueMInt (extract v_11434 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11442 0 1)) (uvalueMInt (extract v_11442 1 9)) (uvalueMInt (extract v_11442 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11452 0 1)) (uvalueMInt (extract v_11452 1 9)) (uvalueMInt (extract v_11452 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11462 0 1)) (uvalueMInt (extract v_11462 1 9)) (uvalueMInt (extract v_11462 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11470 0 1)) (uvalueMInt (extract v_11470 1 9)) (uvalueMInt (extract v_11470 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11480 0 1)) (uvalueMInt (extract v_11480 1 9)) (uvalueMInt (extract v_11480 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11490 0 1)) (uvalueMInt (extract v_11490 1 9)) (uvalueMInt (extract v_11490 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11498 0 1)) (uvalueMInt (extract v_11498 1 9)) (uvalueMInt (extract v_11498 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11508 0 1)) (uvalueMInt (extract v_11508 1 9)) (uvalueMInt (extract v_11508 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11518 0 1)) (uvalueMInt (extract v_11518 1 9)) (uvalueMInt (extract v_11518 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11526 0 1)) (uvalueMInt (extract v_11526 1 9)) (uvalueMInt (extract v_11526 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11536 0 1)) (uvalueMInt (extract v_11536 1 9)) (uvalueMInt (extract v_11536 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11546 0 1)) (uvalueMInt (extract v_11546 1 9)) (uvalueMInt (extract v_11546 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11554 0 1)) (uvalueMInt (extract v_11554 1 9)) (uvalueMInt (extract v_11554 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11564 0 1)) (uvalueMInt (extract v_11564 1 9)) (uvalueMInt (extract v_11564 9 32)))) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3308 : Mem) (v_3306 : reg (bv 128)) (v_3307 : reg (bv 128)) => do
      v_21834 <- getRegister v_3307;
      v_21835 <- eval (extract v_21834 0 32);
      v_21843 <- evaluateAddress v_3308;
      v_21844 <- load v_21843 16;
      v_21845 <- eval (extract v_21844 0 32);
      v_21855 <- getRegister v_3306;
      v_21856 <- eval (extract v_21855 0 32);
      v_21866 <- eval (extract v_21834 32 64);
      v_21874 <- eval (extract v_21844 32 64);
      v_21884 <- eval (extract v_21855 32 64);
      v_21894 <- eval (extract v_21834 64 96);
      v_21902 <- eval (extract v_21844 64 96);
      v_21912 <- eval (extract v_21855 64 96);
      v_21922 <- eval (extract v_21834 96 128);
      v_21930 <- eval (extract v_21844 96 128);
      v_21940 <- eval (extract v_21855 96 128);
      setRegister (lhs.of_reg v_3307) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21835 0 1)) (uvalueMInt (extract v_21835 1 9)) (uvalueMInt (extract v_21835 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21845 0 1)) (uvalueMInt (extract v_21845 1 9)) (uvalueMInt (extract v_21845 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21856 0 1)) (uvalueMInt (extract v_21856 1 9)) (uvalueMInt (extract v_21856 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21866 0 1)) (uvalueMInt (extract v_21866 1 9)) (uvalueMInt (extract v_21866 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21874 0 1)) (uvalueMInt (extract v_21874 1 9)) (uvalueMInt (extract v_21874 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21884 0 1)) (uvalueMInt (extract v_21884 1 9)) (uvalueMInt (extract v_21884 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21894 0 1)) (uvalueMInt (extract v_21894 1 9)) (uvalueMInt (extract v_21894 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21902 0 1)) (uvalueMInt (extract v_21902 1 9)) (uvalueMInt (extract v_21902 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21912 0 1)) (uvalueMInt (extract v_21912 1 9)) (uvalueMInt (extract v_21912 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21922 0 1)) (uvalueMInt (extract v_21922 1 9)) (uvalueMInt (extract v_21922 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21930 0 1)) (uvalueMInt (extract v_21930 1 9)) (uvalueMInt (extract v_21930 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21940 0 1)) (uvalueMInt (extract v_21940 1 9)) (uvalueMInt (extract v_21940 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_3317 : Mem) (v_3318 : reg (bv 256)) (v_3319 : reg (bv 256)) => do
      v_21954 <- getRegister v_3319;
      v_21955 <- eval (extract v_21954 0 32);
      v_21963 <- evaluateAddress v_3317;
      v_21964 <- load v_21963 32;
      v_21965 <- eval (extract v_21964 0 32);
      v_21975 <- getRegister v_3318;
      v_21976 <- eval (extract v_21975 0 32);
      v_21986 <- eval (extract v_21954 32 64);
      v_21994 <- eval (extract v_21964 32 64);
      v_22004 <- eval (extract v_21975 32 64);
      v_22014 <- eval (extract v_21954 64 96);
      v_22022 <- eval (extract v_21964 64 96);
      v_22032 <- eval (extract v_21975 64 96);
      v_22042 <- eval (extract v_21954 96 128);
      v_22050 <- eval (extract v_21964 96 128);
      v_22060 <- eval (extract v_21975 96 128);
      v_22070 <- eval (extract v_21954 128 160);
      v_22078 <- eval (extract v_21964 128 160);
      v_22088 <- eval (extract v_21975 128 160);
      v_22098 <- eval (extract v_21954 160 192);
      v_22106 <- eval (extract v_21964 160 192);
      v_22116 <- eval (extract v_21975 160 192);
      v_22126 <- eval (extract v_21954 192 224);
      v_22134 <- eval (extract v_21964 192 224);
      v_22144 <- eval (extract v_21975 192 224);
      v_22154 <- eval (extract v_21954 224 256);
      v_22162 <- eval (extract v_21964 224 256);
      v_22172 <- eval (extract v_21975 224 256);
      setRegister (lhs.of_reg v_3319) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21955 0 1)) (uvalueMInt (extract v_21955 1 9)) (uvalueMInt (extract v_21955 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21965 0 1)) (uvalueMInt (extract v_21965 1 9)) (uvalueMInt (extract v_21965 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21976 0 1)) (uvalueMInt (extract v_21976 1 9)) (uvalueMInt (extract v_21976 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21986 0 1)) (uvalueMInt (extract v_21986 1 9)) (uvalueMInt (extract v_21986 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21994 0 1)) (uvalueMInt (extract v_21994 1 9)) (uvalueMInt (extract v_21994 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22004 0 1)) (uvalueMInt (extract v_22004 1 9)) (uvalueMInt (extract v_22004 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22014 0 1)) (uvalueMInt (extract v_22014 1 9)) (uvalueMInt (extract v_22014 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22022 0 1)) (uvalueMInt (extract v_22022 1 9)) (uvalueMInt (extract v_22022 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22032 0 1)) (uvalueMInt (extract v_22032 1 9)) (uvalueMInt (extract v_22032 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22042 0 1)) (uvalueMInt (extract v_22042 1 9)) (uvalueMInt (extract v_22042 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22050 0 1)) (uvalueMInt (extract v_22050 1 9)) (uvalueMInt (extract v_22050 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22060 0 1)) (uvalueMInt (extract v_22060 1 9)) (uvalueMInt (extract v_22060 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22070 0 1)) (uvalueMInt (extract v_22070 1 9)) (uvalueMInt (extract v_22070 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22078 0 1)) (uvalueMInt (extract v_22078 1 9)) (uvalueMInt (extract v_22078 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22088 0 1)) (uvalueMInt (extract v_22088 1 9)) (uvalueMInt (extract v_22088 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22098 0 1)) (uvalueMInt (extract v_22098 1 9)) (uvalueMInt (extract v_22098 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22106 0 1)) (uvalueMInt (extract v_22106 1 9)) (uvalueMInt (extract v_22106 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22116 0 1)) (uvalueMInt (extract v_22116 1 9)) (uvalueMInt (extract v_22116 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22126 0 1)) (uvalueMInt (extract v_22126 1 9)) (uvalueMInt (extract v_22126 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22134 0 1)) (uvalueMInt (extract v_22134 1 9)) (uvalueMInt (extract v_22134 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22144 0 1)) (uvalueMInt (extract v_22144 1 9)) (uvalueMInt (extract v_22144 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22154 0 1)) (uvalueMInt (extract v_22154 1 9)) (uvalueMInt (extract v_22154 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22162 0 1)) (uvalueMInt (extract v_22162 1 9)) (uvalueMInt (extract v_22162 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22172 0 1)) (uvalueMInt (extract v_22172 1 9)) (uvalueMInt (extract v_22172 9 32)))) 32))))))));
      pure ()
    pat_end
