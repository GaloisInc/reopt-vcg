def vfmsub231ps1 : instruction :=
  definst "vfmsub231ps" $ do
    pattern fun (v_2915 : reg (bv 128)) (v_2916 : reg (bv 128)) (v_2917 : reg (bv 128)) => do
      v_8581 <- getRegister v_2916;
      v_8582 <- eval (extract v_8581 0 32);
      v_8590 <- getRegister v_2915;
      v_8591 <- eval (extract v_8590 0 32);
      v_8600 <- getRegister v_2917;
      v_8601 <- eval (extract v_8600 0 32);
      v_8611 <- eval (extract v_8581 32 64);
      v_8619 <- eval (extract v_8590 32 64);
      v_8628 <- eval (extract v_8600 32 64);
      v_8638 <- eval (extract v_8581 64 96);
      v_8646 <- eval (extract v_8590 64 96);
      v_8655 <- eval (extract v_8600 64 96);
      v_8665 <- eval (extract v_8581 96 128);
      v_8673 <- eval (extract v_8590 96 128);
      v_8682 <- eval (extract v_8600 96 128);
      setRegister (lhs.of_reg v_2917) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8582 0 1)) (uvalueMInt (extract v_8582 1 9)) (uvalueMInt (extract v_8582 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8591 0 1)) (uvalueMInt (extract v_8591 1 9)) (uvalueMInt (extract v_8591 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8601 0 1)) (uvalueMInt (extract v_8601 1 9)) (uvalueMInt (extract v_8601 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8611 0 1)) (uvalueMInt (extract v_8611 1 9)) (uvalueMInt (extract v_8611 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8619 0 1)) (uvalueMInt (extract v_8619 1 9)) (uvalueMInt (extract v_8619 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8628 0 1)) (uvalueMInt (extract v_8628 1 9)) (uvalueMInt (extract v_8628 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8638 0 1)) (uvalueMInt (extract v_8638 1 9)) (uvalueMInt (extract v_8638 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8646 0 1)) (uvalueMInt (extract v_8646 1 9)) (uvalueMInt (extract v_8646 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8655 0 1)) (uvalueMInt (extract v_8655 1 9)) (uvalueMInt (extract v_8655 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8665 0 1)) (uvalueMInt (extract v_8665 1 9)) (uvalueMInt (extract v_8665 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8673 0 1)) (uvalueMInt (extract v_8673 1 9)) (uvalueMInt (extract v_8673 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8682 0 1)) (uvalueMInt (extract v_8682 1 9)) (uvalueMInt (extract v_8682 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_2926 : reg (bv 256)) (v_2927 : reg (bv 256)) (v_2928 : reg (bv 256)) => do
      v_8701 <- getRegister v_2927;
      v_8702 <- eval (extract v_8701 0 32);
      v_8710 <- getRegister v_2926;
      v_8711 <- eval (extract v_8710 0 32);
      v_8720 <- getRegister v_2928;
      v_8721 <- eval (extract v_8720 0 32);
      v_8731 <- eval (extract v_8701 32 64);
      v_8739 <- eval (extract v_8710 32 64);
      v_8748 <- eval (extract v_8720 32 64);
      v_8758 <- eval (extract v_8701 64 96);
      v_8766 <- eval (extract v_8710 64 96);
      v_8775 <- eval (extract v_8720 64 96);
      v_8785 <- eval (extract v_8701 96 128);
      v_8793 <- eval (extract v_8710 96 128);
      v_8802 <- eval (extract v_8720 96 128);
      v_8812 <- eval (extract v_8701 128 160);
      v_8820 <- eval (extract v_8710 128 160);
      v_8829 <- eval (extract v_8720 128 160);
      v_8839 <- eval (extract v_8701 160 192);
      v_8847 <- eval (extract v_8710 160 192);
      v_8856 <- eval (extract v_8720 160 192);
      v_8866 <- eval (extract v_8701 192 224);
      v_8874 <- eval (extract v_8710 192 224);
      v_8883 <- eval (extract v_8720 192 224);
      v_8893 <- eval (extract v_8701 224 256);
      v_8901 <- eval (extract v_8710 224 256);
      v_8910 <- eval (extract v_8720 224 256);
      setRegister (lhs.of_reg v_2928) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8702 0 1)) (uvalueMInt (extract v_8702 1 9)) (uvalueMInt (extract v_8702 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8711 0 1)) (uvalueMInt (extract v_8711 1 9)) (uvalueMInt (extract v_8711 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8721 0 1)) (uvalueMInt (extract v_8721 1 9)) (uvalueMInt (extract v_8721 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8731 0 1)) (uvalueMInt (extract v_8731 1 9)) (uvalueMInt (extract v_8731 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8739 0 1)) (uvalueMInt (extract v_8739 1 9)) (uvalueMInt (extract v_8739 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8748 0 1)) (uvalueMInt (extract v_8748 1 9)) (uvalueMInt (extract v_8748 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8758 0 1)) (uvalueMInt (extract v_8758 1 9)) (uvalueMInt (extract v_8758 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8766 0 1)) (uvalueMInt (extract v_8766 1 9)) (uvalueMInt (extract v_8766 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8775 0 1)) (uvalueMInt (extract v_8775 1 9)) (uvalueMInt (extract v_8775 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8785 0 1)) (uvalueMInt (extract v_8785 1 9)) (uvalueMInt (extract v_8785 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8793 0 1)) (uvalueMInt (extract v_8793 1 9)) (uvalueMInt (extract v_8793 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8802 0 1)) (uvalueMInt (extract v_8802 1 9)) (uvalueMInt (extract v_8802 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8812 0 1)) (uvalueMInt (extract v_8812 1 9)) (uvalueMInt (extract v_8812 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8820 0 1)) (uvalueMInt (extract v_8820 1 9)) (uvalueMInt (extract v_8820 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8829 0 1)) (uvalueMInt (extract v_8829 1 9)) (uvalueMInt (extract v_8829 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8839 0 1)) (uvalueMInt (extract v_8839 1 9)) (uvalueMInt (extract v_8839 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8847 0 1)) (uvalueMInt (extract v_8847 1 9)) (uvalueMInt (extract v_8847 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8856 0 1)) (uvalueMInt (extract v_8856 1 9)) (uvalueMInt (extract v_8856 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8866 0 1)) (uvalueMInt (extract v_8866 1 9)) (uvalueMInt (extract v_8866 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8874 0 1)) (uvalueMInt (extract v_8874 1 9)) (uvalueMInt (extract v_8874 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8883 0 1)) (uvalueMInt (extract v_8883 1 9)) (uvalueMInt (extract v_8883 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8893 0 1)) (uvalueMInt (extract v_8893 1 9)) (uvalueMInt (extract v_8893 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8901 0 1)) (uvalueMInt (extract v_8901 1 9)) (uvalueMInt (extract v_8901 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8910 0 1)) (uvalueMInt (extract v_8910 1 9)) (uvalueMInt (extract v_8910 9 32)))) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2912 : Mem) (v_2910 : reg (bv 128)) (v_2911 : reg (bv 128)) => do
      v_19344 <- getRegister v_2910;
      v_19345 <- eval (extract v_19344 0 32);
      v_19353 <- evaluateAddress v_2912;
      v_19354 <- load v_19353 16;
      v_19355 <- eval (extract v_19354 0 32);
      v_19364 <- getRegister v_2911;
      v_19365 <- eval (extract v_19364 0 32);
      v_19375 <- eval (extract v_19344 32 64);
      v_19383 <- eval (extract v_19354 32 64);
      v_19392 <- eval (extract v_19364 32 64);
      v_19402 <- eval (extract v_19344 64 96);
      v_19410 <- eval (extract v_19354 64 96);
      v_19419 <- eval (extract v_19364 64 96);
      v_19429 <- eval (extract v_19344 96 128);
      v_19437 <- eval (extract v_19354 96 128);
      v_19446 <- eval (extract v_19364 96 128);
      setRegister (lhs.of_reg v_2911) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19345 0 1)) (uvalueMInt (extract v_19345 1 9)) (uvalueMInt (extract v_19345 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19355 0 1)) (uvalueMInt (extract v_19355 1 9)) (uvalueMInt (extract v_19355 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19365 0 1)) (uvalueMInt (extract v_19365 1 9)) (uvalueMInt (extract v_19365 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19375 0 1)) (uvalueMInt (extract v_19375 1 9)) (uvalueMInt (extract v_19375 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19383 0 1)) (uvalueMInt (extract v_19383 1 9)) (uvalueMInt (extract v_19383 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19392 0 1)) (uvalueMInt (extract v_19392 1 9)) (uvalueMInt (extract v_19392 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19402 0 1)) (uvalueMInt (extract v_19402 1 9)) (uvalueMInt (extract v_19402 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19410 0 1)) (uvalueMInt (extract v_19410 1 9)) (uvalueMInt (extract v_19410 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19419 0 1)) (uvalueMInt (extract v_19419 1 9)) (uvalueMInt (extract v_19419 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19429 0 1)) (uvalueMInt (extract v_19429 1 9)) (uvalueMInt (extract v_19429 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19437 0 1)) (uvalueMInt (extract v_19437 1 9)) (uvalueMInt (extract v_19437 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19446 0 1)) (uvalueMInt (extract v_19446 1 9)) (uvalueMInt (extract v_19446 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_2921 : Mem) (v_2922 : reg (bv 256)) (v_2923 : reg (bv 256)) => do
      v_19460 <- getRegister v_2922;
      v_19461 <- eval (extract v_19460 0 32);
      v_19469 <- evaluateAddress v_2921;
      v_19470 <- load v_19469 32;
      v_19471 <- eval (extract v_19470 0 32);
      v_19480 <- getRegister v_2923;
      v_19481 <- eval (extract v_19480 0 32);
      v_19491 <- eval (extract v_19460 32 64);
      v_19499 <- eval (extract v_19470 32 64);
      v_19508 <- eval (extract v_19480 32 64);
      v_19518 <- eval (extract v_19460 64 96);
      v_19526 <- eval (extract v_19470 64 96);
      v_19535 <- eval (extract v_19480 64 96);
      v_19545 <- eval (extract v_19460 96 128);
      v_19553 <- eval (extract v_19470 96 128);
      v_19562 <- eval (extract v_19480 96 128);
      v_19572 <- eval (extract v_19460 128 160);
      v_19580 <- eval (extract v_19470 128 160);
      v_19589 <- eval (extract v_19480 128 160);
      v_19599 <- eval (extract v_19460 160 192);
      v_19607 <- eval (extract v_19470 160 192);
      v_19616 <- eval (extract v_19480 160 192);
      v_19626 <- eval (extract v_19460 192 224);
      v_19634 <- eval (extract v_19470 192 224);
      v_19643 <- eval (extract v_19480 192 224);
      v_19653 <- eval (extract v_19460 224 256);
      v_19661 <- eval (extract v_19470 224 256);
      v_19670 <- eval (extract v_19480 224 256);
      setRegister (lhs.of_reg v_2923) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19461 0 1)) (uvalueMInt (extract v_19461 1 9)) (uvalueMInt (extract v_19461 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19471 0 1)) (uvalueMInt (extract v_19471 1 9)) (uvalueMInt (extract v_19471 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19481 0 1)) (uvalueMInt (extract v_19481 1 9)) (uvalueMInt (extract v_19481 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19491 0 1)) (uvalueMInt (extract v_19491 1 9)) (uvalueMInt (extract v_19491 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19499 0 1)) (uvalueMInt (extract v_19499 1 9)) (uvalueMInt (extract v_19499 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19508 0 1)) (uvalueMInt (extract v_19508 1 9)) (uvalueMInt (extract v_19508 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19518 0 1)) (uvalueMInt (extract v_19518 1 9)) (uvalueMInt (extract v_19518 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19526 0 1)) (uvalueMInt (extract v_19526 1 9)) (uvalueMInt (extract v_19526 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19535 0 1)) (uvalueMInt (extract v_19535 1 9)) (uvalueMInt (extract v_19535 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19545 0 1)) (uvalueMInt (extract v_19545 1 9)) (uvalueMInt (extract v_19545 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19553 0 1)) (uvalueMInt (extract v_19553 1 9)) (uvalueMInt (extract v_19553 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19562 0 1)) (uvalueMInt (extract v_19562 1 9)) (uvalueMInt (extract v_19562 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19572 0 1)) (uvalueMInt (extract v_19572 1 9)) (uvalueMInt (extract v_19572 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19580 0 1)) (uvalueMInt (extract v_19580 1 9)) (uvalueMInt (extract v_19580 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19589 0 1)) (uvalueMInt (extract v_19589 1 9)) (uvalueMInt (extract v_19589 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19599 0 1)) (uvalueMInt (extract v_19599 1 9)) (uvalueMInt (extract v_19599 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19607 0 1)) (uvalueMInt (extract v_19607 1 9)) (uvalueMInt (extract v_19607 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19616 0 1)) (uvalueMInt (extract v_19616 1 9)) (uvalueMInt (extract v_19616 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19626 0 1)) (uvalueMInt (extract v_19626 1 9)) (uvalueMInt (extract v_19626 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19634 0 1)) (uvalueMInt (extract v_19634 1 9)) (uvalueMInt (extract v_19634 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19643 0 1)) (uvalueMInt (extract v_19643 1 9)) (uvalueMInt (extract v_19643 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19653 0 1)) (uvalueMInt (extract v_19653 1 9)) (uvalueMInt (extract v_19653 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19661 0 1)) (uvalueMInt (extract v_19661 1 9)) (uvalueMInt (extract v_19661 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19670 0 1)) (uvalueMInt (extract v_19670 1 9)) (uvalueMInt (extract v_19670 9 32)))) 32))))))));
      pure ()
    pat_end
