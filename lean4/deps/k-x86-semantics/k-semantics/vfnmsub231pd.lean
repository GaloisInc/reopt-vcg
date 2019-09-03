def vfnmsub231pd1 : instruction :=
  definst "vfnmsub231pd" $ do
    pattern fun (v_3421 : reg (bv 128)) (v_3422 : reg (bv 128)) (v_3423 : reg (bv 128)) => do
      v_12297 <- getRegister v_3422;
      v_12298 <- eval (extract v_12297 0 64);
      v_12306 <- getRegister v_3421;
      v_12307 <- eval (extract v_12306 0 64);
      v_12317 <- getRegister v_3423;
      v_12318 <- eval (extract v_12317 0 64);
      v_12328 <- eval (extract v_12297 64 128);
      v_12336 <- eval (extract v_12306 64 128);
      v_12346 <- eval (extract v_12317 64 128);
      setRegister (lhs.of_reg v_3423) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12298 0 1)) (uvalueMInt (extract v_12298 1 12)) (uvalueMInt (extract v_12298 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12307 0 1)) (uvalueMInt (extract v_12307 1 12)) (uvalueMInt (extract v_12307 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12318 0 1)) (uvalueMInt (extract v_12318 1 12)) (uvalueMInt (extract v_12318 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12328 0 1)) (uvalueMInt (extract v_12328 1 12)) (uvalueMInt (extract v_12328 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12336 0 1)) (uvalueMInt (extract v_12336 1 12)) (uvalueMInt (extract v_12336 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12346 0 1)) (uvalueMInt (extract v_12346 1 12)) (uvalueMInt (extract v_12346 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_3432 : reg (bv 256)) (v_3433 : reg (bv 256)) (v_3434 : reg (bv 256)) => do
      v_12363 <- getRegister v_3433;
      v_12364 <- eval (extract v_12363 0 64);
      v_12372 <- getRegister v_3432;
      v_12373 <- eval (extract v_12372 0 64);
      v_12383 <- getRegister v_3434;
      v_12384 <- eval (extract v_12383 0 64);
      v_12394 <- eval (extract v_12363 64 128);
      v_12402 <- eval (extract v_12372 64 128);
      v_12412 <- eval (extract v_12383 64 128);
      v_12422 <- eval (extract v_12363 128 192);
      v_12430 <- eval (extract v_12372 128 192);
      v_12440 <- eval (extract v_12383 128 192);
      v_12450 <- eval (extract v_12363 192 256);
      v_12458 <- eval (extract v_12372 192 256);
      v_12468 <- eval (extract v_12383 192 256);
      setRegister (lhs.of_reg v_3434) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12364 0 1)) (uvalueMInt (extract v_12364 1 12)) (uvalueMInt (extract v_12364 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12373 0 1)) (uvalueMInt (extract v_12373 1 12)) (uvalueMInt (extract v_12373 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12384 0 1)) (uvalueMInt (extract v_12384 1 12)) (uvalueMInt (extract v_12384 12 64)))) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12394 0 1)) (uvalueMInt (extract v_12394 1 12)) (uvalueMInt (extract v_12394 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12402 0 1)) (uvalueMInt (extract v_12402 1 12)) (uvalueMInt (extract v_12402 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12412 0 1)) (uvalueMInt (extract v_12412 1 12)) (uvalueMInt (extract v_12412 12 64)))) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12422 0 1)) (uvalueMInt (extract v_12422 1 12)) (uvalueMInt (extract v_12422 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12430 0 1)) (uvalueMInt (extract v_12430 1 12)) (uvalueMInt (extract v_12430 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12440 0 1)) (uvalueMInt (extract v_12440 1 12)) (uvalueMInt (extract v_12440 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12450 0 1)) (uvalueMInt (extract v_12450 1 12)) (uvalueMInt (extract v_12450 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12458 0 1)) (uvalueMInt (extract v_12458 1 12)) (uvalueMInt (extract v_12458 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12468 0 1)) (uvalueMInt (extract v_12468 1 12)) (uvalueMInt (extract v_12468 12 64)))) 64))));
      pure ()
    pat_end;
    pattern fun (v_3418 : Mem) (v_3416 : reg (bv 128)) (v_3417 : reg (bv 128)) => do
      v_22864 <- getRegister v_3416;
      v_22865 <- eval (extract v_22864 0 64);
      v_22873 <- evaluateAddress v_3418;
      v_22874 <- load v_22873 16;
      v_22875 <- eval (extract v_22874 0 64);
      v_22885 <- getRegister v_3417;
      v_22886 <- eval (extract v_22885 0 64);
      v_22896 <- eval (extract v_22864 64 128);
      v_22904 <- eval (extract v_22874 64 128);
      v_22914 <- eval (extract v_22885 64 128);
      setRegister (lhs.of_reg v_3417) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22865 0 1)) (uvalueMInt (extract v_22865 1 12)) (uvalueMInt (extract v_22865 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22875 0 1)) (uvalueMInt (extract v_22875 1 12)) (uvalueMInt (extract v_22875 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22886 0 1)) (uvalueMInt (extract v_22886 1 12)) (uvalueMInt (extract v_22886 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22896 0 1)) (uvalueMInt (extract v_22896 1 12)) (uvalueMInt (extract v_22896 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22904 0 1)) (uvalueMInt (extract v_22904 1 12)) (uvalueMInt (extract v_22904 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22914 0 1)) (uvalueMInt (extract v_22914 1 12)) (uvalueMInt (extract v_22914 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_3427 : Mem) (v_3428 : reg (bv 256)) (v_3429 : reg (bv 256)) => do
      v_22926 <- getRegister v_3428;
      v_22927 <- eval (extract v_22926 0 64);
      v_22935 <- evaluateAddress v_3427;
      v_22936 <- load v_22935 32;
      v_22937 <- eval (extract v_22936 0 64);
      v_22947 <- getRegister v_3429;
      v_22948 <- eval (extract v_22947 0 64);
      v_22958 <- eval (extract v_22926 64 128);
      v_22966 <- eval (extract v_22936 64 128);
      v_22976 <- eval (extract v_22947 64 128);
      v_22986 <- eval (extract v_22926 128 192);
      v_22994 <- eval (extract v_22936 128 192);
      v_23004 <- eval (extract v_22947 128 192);
      v_23014 <- eval (extract v_22926 192 256);
      v_23022 <- eval (extract v_22936 192 256);
      v_23032 <- eval (extract v_22947 192 256);
      setRegister (lhs.of_reg v_3429) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22927 0 1)) (uvalueMInt (extract v_22927 1 12)) (uvalueMInt (extract v_22927 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22937 0 1)) (uvalueMInt (extract v_22937 1 12)) (uvalueMInt (extract v_22937 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22948 0 1)) (uvalueMInt (extract v_22948 1 12)) (uvalueMInt (extract v_22948 12 64)))) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22958 0 1)) (uvalueMInt (extract v_22958 1 12)) (uvalueMInt (extract v_22958 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22966 0 1)) (uvalueMInt (extract v_22966 1 12)) (uvalueMInt (extract v_22966 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22976 0 1)) (uvalueMInt (extract v_22976 1 12)) (uvalueMInt (extract v_22976 12 64)))) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22986 0 1)) (uvalueMInt (extract v_22986 1 12)) (uvalueMInt (extract v_22986 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22994 0 1)) (uvalueMInt (extract v_22994 1 12)) (uvalueMInt (extract v_22994 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_23004 0 1)) (uvalueMInt (extract v_23004 1 12)) (uvalueMInt (extract v_23004 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_23014 0 1)) (uvalueMInt (extract v_23014 1 12)) (uvalueMInt (extract v_23014 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_23022 0 1)) (uvalueMInt (extract v_23022 1 12)) (uvalueMInt (extract v_23022 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_23032 0 1)) (uvalueMInt (extract v_23032 1 12)) (uvalueMInt (extract v_23032 12 64)))) 64))));
      pure ()
    pat_end
