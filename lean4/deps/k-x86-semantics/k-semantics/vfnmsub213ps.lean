def vfnmsub213ps1 : instruction :=
  definst "vfnmsub213ps" $ do
    pattern fun (v_3377 : reg (bv 128)) (v_3378 : reg (bv 128)) (v_3379 : reg (bv 128)) => do
      v_11855 <- getRegister v_3378;
      v_11856 <- eval (extract v_11855 0 32);
      v_11864 <- getRegister v_3379;
      v_11865 <- eval (extract v_11864 0 32);
      v_11875 <- getRegister v_3377;
      v_11876 <- eval (extract v_11875 0 32);
      v_11886 <- eval (extract v_11855 32 64);
      v_11894 <- eval (extract v_11864 32 64);
      v_11904 <- eval (extract v_11875 32 64);
      v_11914 <- eval (extract v_11855 64 96);
      v_11922 <- eval (extract v_11864 64 96);
      v_11932 <- eval (extract v_11875 64 96);
      v_11942 <- eval (extract v_11855 96 128);
      v_11950 <- eval (extract v_11864 96 128);
      v_11960 <- eval (extract v_11875 96 128);
      setRegister (lhs.of_reg v_3379) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11856 0 1)) (uvalueMInt (extract v_11856 1 9)) (uvalueMInt (extract v_11856 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11865 0 1)) (uvalueMInt (extract v_11865 1 9)) (uvalueMInt (extract v_11865 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11876 0 1)) (uvalueMInt (extract v_11876 1 9)) (uvalueMInt (extract v_11876 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11886 0 1)) (uvalueMInt (extract v_11886 1 9)) (uvalueMInt (extract v_11886 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11894 0 1)) (uvalueMInt (extract v_11894 1 9)) (uvalueMInt (extract v_11894 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11904 0 1)) (uvalueMInt (extract v_11904 1 9)) (uvalueMInt (extract v_11904 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11914 0 1)) (uvalueMInt (extract v_11914 1 9)) (uvalueMInt (extract v_11914 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11922 0 1)) (uvalueMInt (extract v_11922 1 9)) (uvalueMInt (extract v_11922 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11932 0 1)) (uvalueMInt (extract v_11932 1 9)) (uvalueMInt (extract v_11932 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11942 0 1)) (uvalueMInt (extract v_11942 1 9)) (uvalueMInt (extract v_11942 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11950 0 1)) (uvalueMInt (extract v_11950 1 9)) (uvalueMInt (extract v_11950 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11960 0 1)) (uvalueMInt (extract v_11960 1 9)) (uvalueMInt (extract v_11960 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_3388 : reg (bv 256)) (v_3389 : reg (bv 256)) (v_3390 : reg (bv 256)) => do
      v_11979 <- getRegister v_3389;
      v_11980 <- eval (extract v_11979 0 32);
      v_11988 <- getRegister v_3390;
      v_11989 <- eval (extract v_11988 0 32);
      v_11999 <- getRegister v_3388;
      v_12000 <- eval (extract v_11999 0 32);
      v_12010 <- eval (extract v_11979 32 64);
      v_12018 <- eval (extract v_11988 32 64);
      v_12028 <- eval (extract v_11999 32 64);
      v_12038 <- eval (extract v_11979 64 96);
      v_12046 <- eval (extract v_11988 64 96);
      v_12056 <- eval (extract v_11999 64 96);
      v_12066 <- eval (extract v_11979 96 128);
      v_12074 <- eval (extract v_11988 96 128);
      v_12084 <- eval (extract v_11999 96 128);
      v_12094 <- eval (extract v_11979 128 160);
      v_12102 <- eval (extract v_11988 128 160);
      v_12112 <- eval (extract v_11999 128 160);
      v_12122 <- eval (extract v_11979 160 192);
      v_12130 <- eval (extract v_11988 160 192);
      v_12140 <- eval (extract v_11999 160 192);
      v_12150 <- eval (extract v_11979 192 224);
      v_12158 <- eval (extract v_11988 192 224);
      v_12168 <- eval (extract v_11999 192 224);
      v_12178 <- eval (extract v_11979 224 256);
      v_12186 <- eval (extract v_11988 224 256);
      v_12196 <- eval (extract v_11999 224 256);
      setRegister (lhs.of_reg v_3390) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11980 0 1)) (uvalueMInt (extract v_11980 1 9)) (uvalueMInt (extract v_11980 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11989 0 1)) (uvalueMInt (extract v_11989 1 9)) (uvalueMInt (extract v_11989 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12000 0 1)) (uvalueMInt (extract v_12000 1 9)) (uvalueMInt (extract v_12000 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12010 0 1)) (uvalueMInt (extract v_12010 1 9)) (uvalueMInt (extract v_12010 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12018 0 1)) (uvalueMInt (extract v_12018 1 9)) (uvalueMInt (extract v_12018 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12028 0 1)) (uvalueMInt (extract v_12028 1 9)) (uvalueMInt (extract v_12028 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12038 0 1)) (uvalueMInt (extract v_12038 1 9)) (uvalueMInt (extract v_12038 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12046 0 1)) (uvalueMInt (extract v_12046 1 9)) (uvalueMInt (extract v_12046 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12056 0 1)) (uvalueMInt (extract v_12056 1 9)) (uvalueMInt (extract v_12056 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12066 0 1)) (uvalueMInt (extract v_12066 1 9)) (uvalueMInt (extract v_12066 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12074 0 1)) (uvalueMInt (extract v_12074 1 9)) (uvalueMInt (extract v_12074 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12084 0 1)) (uvalueMInt (extract v_12084 1 9)) (uvalueMInt (extract v_12084 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12094 0 1)) (uvalueMInt (extract v_12094 1 9)) (uvalueMInt (extract v_12094 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12102 0 1)) (uvalueMInt (extract v_12102 1 9)) (uvalueMInt (extract v_12102 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12112 0 1)) (uvalueMInt (extract v_12112 1 9)) (uvalueMInt (extract v_12112 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12122 0 1)) (uvalueMInt (extract v_12122 1 9)) (uvalueMInt (extract v_12122 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12130 0 1)) (uvalueMInt (extract v_12130 1 9)) (uvalueMInt (extract v_12130 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12140 0 1)) (uvalueMInt (extract v_12140 1 9)) (uvalueMInt (extract v_12140 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12150 0 1)) (uvalueMInt (extract v_12150 1 9)) (uvalueMInt (extract v_12150 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12158 0 1)) (uvalueMInt (extract v_12158 1 9)) (uvalueMInt (extract v_12158 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12168 0 1)) (uvalueMInt (extract v_12168 1 9)) (uvalueMInt (extract v_12168 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12178 0 1)) (uvalueMInt (extract v_12178 1 9)) (uvalueMInt (extract v_12178 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12186 0 1)) (uvalueMInt (extract v_12186 1 9)) (uvalueMInt (extract v_12186 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12196 0 1)) (uvalueMInt (extract v_12196 1 9)) (uvalueMInt (extract v_12196 9 32)))) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3374 : Mem) (v_3372 : reg (bv 128)) (v_3373 : reg (bv 128)) => do
      v_22440 <- getRegister v_3372;
      v_22441 <- eval (extract v_22440 0 32);
      v_22449 <- getRegister v_3373;
      v_22450 <- eval (extract v_22449 0 32);
      v_22460 <- evaluateAddress v_3374;
      v_22461 <- load v_22460 16;
      v_22462 <- eval (extract v_22461 0 32);
      v_22472 <- eval (extract v_22440 32 64);
      v_22480 <- eval (extract v_22449 32 64);
      v_22490 <- eval (extract v_22461 32 64);
      v_22500 <- eval (extract v_22440 64 96);
      v_22508 <- eval (extract v_22449 64 96);
      v_22518 <- eval (extract v_22461 64 96);
      v_22528 <- eval (extract v_22440 96 128);
      v_22536 <- eval (extract v_22449 96 128);
      v_22546 <- eval (extract v_22461 96 128);
      setRegister (lhs.of_reg v_3373) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22441 0 1)) (uvalueMInt (extract v_22441 1 9)) (uvalueMInt (extract v_22441 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22450 0 1)) (uvalueMInt (extract v_22450 1 9)) (uvalueMInt (extract v_22450 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22462 0 1)) (uvalueMInt (extract v_22462 1 9)) (uvalueMInt (extract v_22462 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22472 0 1)) (uvalueMInt (extract v_22472 1 9)) (uvalueMInt (extract v_22472 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22480 0 1)) (uvalueMInt (extract v_22480 1 9)) (uvalueMInt (extract v_22480 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22490 0 1)) (uvalueMInt (extract v_22490 1 9)) (uvalueMInt (extract v_22490 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22500 0 1)) (uvalueMInt (extract v_22500 1 9)) (uvalueMInt (extract v_22500 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22508 0 1)) (uvalueMInt (extract v_22508 1 9)) (uvalueMInt (extract v_22508 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22518 0 1)) (uvalueMInt (extract v_22518 1 9)) (uvalueMInt (extract v_22518 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22528 0 1)) (uvalueMInt (extract v_22528 1 9)) (uvalueMInt (extract v_22528 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22536 0 1)) (uvalueMInt (extract v_22536 1 9)) (uvalueMInt (extract v_22536 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22546 0 1)) (uvalueMInt (extract v_22546 1 9)) (uvalueMInt (extract v_22546 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_3383 : Mem) (v_3384 : reg (bv 256)) (v_3385 : reg (bv 256)) => do
      v_22560 <- getRegister v_3384;
      v_22561 <- eval (extract v_22560 0 32);
      v_22569 <- getRegister v_3385;
      v_22570 <- eval (extract v_22569 0 32);
      v_22580 <- evaluateAddress v_3383;
      v_22581 <- load v_22580 32;
      v_22582 <- eval (extract v_22581 0 32);
      v_22592 <- eval (extract v_22560 32 64);
      v_22600 <- eval (extract v_22569 32 64);
      v_22610 <- eval (extract v_22581 32 64);
      v_22620 <- eval (extract v_22560 64 96);
      v_22628 <- eval (extract v_22569 64 96);
      v_22638 <- eval (extract v_22581 64 96);
      v_22648 <- eval (extract v_22560 96 128);
      v_22656 <- eval (extract v_22569 96 128);
      v_22666 <- eval (extract v_22581 96 128);
      v_22676 <- eval (extract v_22560 128 160);
      v_22684 <- eval (extract v_22569 128 160);
      v_22694 <- eval (extract v_22581 128 160);
      v_22704 <- eval (extract v_22560 160 192);
      v_22712 <- eval (extract v_22569 160 192);
      v_22722 <- eval (extract v_22581 160 192);
      v_22732 <- eval (extract v_22560 192 224);
      v_22740 <- eval (extract v_22569 192 224);
      v_22750 <- eval (extract v_22581 192 224);
      v_22760 <- eval (extract v_22560 224 256);
      v_22768 <- eval (extract v_22569 224 256);
      v_22778 <- eval (extract v_22581 224 256);
      setRegister (lhs.of_reg v_3385) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22561 0 1)) (uvalueMInt (extract v_22561 1 9)) (uvalueMInt (extract v_22561 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22570 0 1)) (uvalueMInt (extract v_22570 1 9)) (uvalueMInt (extract v_22570 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22582 0 1)) (uvalueMInt (extract v_22582 1 9)) (uvalueMInt (extract v_22582 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22592 0 1)) (uvalueMInt (extract v_22592 1 9)) (uvalueMInt (extract v_22592 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22600 0 1)) (uvalueMInt (extract v_22600 1 9)) (uvalueMInt (extract v_22600 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22610 0 1)) (uvalueMInt (extract v_22610 1 9)) (uvalueMInt (extract v_22610 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22620 0 1)) (uvalueMInt (extract v_22620 1 9)) (uvalueMInt (extract v_22620 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22628 0 1)) (uvalueMInt (extract v_22628 1 9)) (uvalueMInt (extract v_22628 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22638 0 1)) (uvalueMInt (extract v_22638 1 9)) (uvalueMInt (extract v_22638 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22648 0 1)) (uvalueMInt (extract v_22648 1 9)) (uvalueMInt (extract v_22648 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22656 0 1)) (uvalueMInt (extract v_22656 1 9)) (uvalueMInt (extract v_22656 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22666 0 1)) (uvalueMInt (extract v_22666 1 9)) (uvalueMInt (extract v_22666 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22676 0 1)) (uvalueMInt (extract v_22676 1 9)) (uvalueMInt (extract v_22676 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22684 0 1)) (uvalueMInt (extract v_22684 1 9)) (uvalueMInt (extract v_22684 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22694 0 1)) (uvalueMInt (extract v_22694 1 9)) (uvalueMInt (extract v_22694 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22704 0 1)) (uvalueMInt (extract v_22704 1 9)) (uvalueMInt (extract v_22704 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22712 0 1)) (uvalueMInt (extract v_22712 1 9)) (uvalueMInt (extract v_22712 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22722 0 1)) (uvalueMInt (extract v_22722 1 9)) (uvalueMInt (extract v_22722 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22732 0 1)) (uvalueMInt (extract v_22732 1 9)) (uvalueMInt (extract v_22732 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22740 0 1)) (uvalueMInt (extract v_22740 1 9)) (uvalueMInt (extract v_22740 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22750 0 1)) (uvalueMInt (extract v_22750 1 9)) (uvalueMInt (extract v_22750 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22760 0 1)) (uvalueMInt (extract v_22760 1 9)) (uvalueMInt (extract v_22760 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22768 0 1)) (uvalueMInt (extract v_22768 1 9)) (uvalueMInt (extract v_22768 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22778 0 1)) (uvalueMInt (extract v_22778 1 9)) (uvalueMInt (extract v_22778 9 32)))) 32))))))));
      pure ()
    pat_end
