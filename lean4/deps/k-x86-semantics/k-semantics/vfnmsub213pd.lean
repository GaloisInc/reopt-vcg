def vfnmsub213pd1 : instruction :=
  definst "vfnmsub213pd" $ do
    pattern fun (v_3355 : reg (bv 128)) (v_3356 : reg (bv 128)) (v_3357 : reg (bv 128)) => do
      v_11665 <- getRegister v_3356;
      v_11666 <- eval (extract v_11665 0 64);
      v_11674 <- getRegister v_3357;
      v_11675 <- eval (extract v_11674 0 64);
      v_11685 <- getRegister v_3355;
      v_11686 <- eval (extract v_11685 0 64);
      v_11696 <- eval (extract v_11665 64 128);
      v_11704 <- eval (extract v_11674 64 128);
      v_11714 <- eval (extract v_11685 64 128);
      setRegister (lhs.of_reg v_3357) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11666 0 1)) (uvalueMInt (extract v_11666 1 12)) (uvalueMInt (extract v_11666 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11675 0 1)) (uvalueMInt (extract v_11675 1 12)) (uvalueMInt (extract v_11675 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11686 0 1)) (uvalueMInt (extract v_11686 1 12)) (uvalueMInt (extract v_11686 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11696 0 1)) (uvalueMInt (extract v_11696 1 12)) (uvalueMInt (extract v_11696 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11704 0 1)) (uvalueMInt (extract v_11704 1 12)) (uvalueMInt (extract v_11704 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11714 0 1)) (uvalueMInt (extract v_11714 1 12)) (uvalueMInt (extract v_11714 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_3366 : reg (bv 256)) (v_3367 : reg (bv 256)) (v_3368 : reg (bv 256)) => do
      v_11731 <- getRegister v_3367;
      v_11732 <- eval (extract v_11731 0 64);
      v_11740 <- getRegister v_3368;
      v_11741 <- eval (extract v_11740 0 64);
      v_11751 <- getRegister v_3366;
      v_11752 <- eval (extract v_11751 0 64);
      v_11762 <- eval (extract v_11731 64 128);
      v_11770 <- eval (extract v_11740 64 128);
      v_11780 <- eval (extract v_11751 64 128);
      v_11790 <- eval (extract v_11731 128 192);
      v_11798 <- eval (extract v_11740 128 192);
      v_11808 <- eval (extract v_11751 128 192);
      v_11818 <- eval (extract v_11731 192 256);
      v_11826 <- eval (extract v_11740 192 256);
      v_11836 <- eval (extract v_11751 192 256);
      setRegister (lhs.of_reg v_3368) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11732 0 1)) (uvalueMInt (extract v_11732 1 12)) (uvalueMInt (extract v_11732 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11741 0 1)) (uvalueMInt (extract v_11741 1 12)) (uvalueMInt (extract v_11741 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11752 0 1)) (uvalueMInt (extract v_11752 1 12)) (uvalueMInt (extract v_11752 12 64)))) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11762 0 1)) (uvalueMInt (extract v_11762 1 12)) (uvalueMInt (extract v_11762 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11770 0 1)) (uvalueMInt (extract v_11770 1 12)) (uvalueMInt (extract v_11770 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11780 0 1)) (uvalueMInt (extract v_11780 1 12)) (uvalueMInt (extract v_11780 12 64)))) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11790 0 1)) (uvalueMInt (extract v_11790 1 12)) (uvalueMInt (extract v_11790 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11798 0 1)) (uvalueMInt (extract v_11798 1 12)) (uvalueMInt (extract v_11798 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11808 0 1)) (uvalueMInt (extract v_11808 1 12)) (uvalueMInt (extract v_11808 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11818 0 1)) (uvalueMInt (extract v_11818 1 12)) (uvalueMInt (extract v_11818 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11826 0 1)) (uvalueMInt (extract v_11826 1 12)) (uvalueMInt (extract v_11826 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11836 0 1)) (uvalueMInt (extract v_11836 1 12)) (uvalueMInt (extract v_11836 12 64)))) 64))));
      pure ()
    pat_end;
    pattern fun (v_3352 : Mem) (v_3350 : reg (bv 128)) (v_3351 : reg (bv 128)) => do
      v_22258 <- getRegister v_3350;
      v_22259 <- eval (extract v_22258 0 64);
      v_22267 <- getRegister v_3351;
      v_22268 <- eval (extract v_22267 0 64);
      v_22278 <- evaluateAddress v_3352;
      v_22279 <- load v_22278 16;
      v_22280 <- eval (extract v_22279 0 64);
      v_22290 <- eval (extract v_22258 64 128);
      v_22298 <- eval (extract v_22267 64 128);
      v_22308 <- eval (extract v_22279 64 128);
      setRegister (lhs.of_reg v_3351) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22259 0 1)) (uvalueMInt (extract v_22259 1 12)) (uvalueMInt (extract v_22259 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22268 0 1)) (uvalueMInt (extract v_22268 1 12)) (uvalueMInt (extract v_22268 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22280 0 1)) (uvalueMInt (extract v_22280 1 12)) (uvalueMInt (extract v_22280 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22290 0 1)) (uvalueMInt (extract v_22290 1 12)) (uvalueMInt (extract v_22290 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22298 0 1)) (uvalueMInt (extract v_22298 1 12)) (uvalueMInt (extract v_22298 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22308 0 1)) (uvalueMInt (extract v_22308 1 12)) (uvalueMInt (extract v_22308 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_3361 : Mem) (v_3362 : reg (bv 256)) (v_3363 : reg (bv 256)) => do
      v_22320 <- getRegister v_3362;
      v_22321 <- eval (extract v_22320 0 64);
      v_22329 <- getRegister v_3363;
      v_22330 <- eval (extract v_22329 0 64);
      v_22340 <- evaluateAddress v_3361;
      v_22341 <- load v_22340 32;
      v_22342 <- eval (extract v_22341 0 64);
      v_22352 <- eval (extract v_22320 64 128);
      v_22360 <- eval (extract v_22329 64 128);
      v_22370 <- eval (extract v_22341 64 128);
      v_22380 <- eval (extract v_22320 128 192);
      v_22388 <- eval (extract v_22329 128 192);
      v_22398 <- eval (extract v_22341 128 192);
      v_22408 <- eval (extract v_22320 192 256);
      v_22416 <- eval (extract v_22329 192 256);
      v_22426 <- eval (extract v_22341 192 256);
      setRegister (lhs.of_reg v_3363) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22321 0 1)) (uvalueMInt (extract v_22321 1 12)) (uvalueMInt (extract v_22321 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22330 0 1)) (uvalueMInt (extract v_22330 1 12)) (uvalueMInt (extract v_22330 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22342 0 1)) (uvalueMInt (extract v_22342 1 12)) (uvalueMInt (extract v_22342 12 64)))) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22352 0 1)) (uvalueMInt (extract v_22352 1 12)) (uvalueMInt (extract v_22352 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22360 0 1)) (uvalueMInt (extract v_22360 1 12)) (uvalueMInt (extract v_22360 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22370 0 1)) (uvalueMInt (extract v_22370 1 12)) (uvalueMInt (extract v_22370 12 64)))) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22380 0 1)) (uvalueMInt (extract v_22380 1 12)) (uvalueMInt (extract v_22380 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22388 0 1)) (uvalueMInt (extract v_22388 1 12)) (uvalueMInt (extract v_22388 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22398 0 1)) (uvalueMInt (extract v_22398 1 12)) (uvalueMInt (extract v_22398 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22408 0 1)) (uvalueMInt (extract v_22408 1 12)) (uvalueMInt (extract v_22408 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22416 0 1)) (uvalueMInt (extract v_22416 1 12)) (uvalueMInt (extract v_22416 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22426 0 1)) (uvalueMInt (extract v_22426 1 12)) (uvalueMInt (extract v_22426 12 64)))) 64))));
      pure ()
    pat_end
