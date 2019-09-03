def vfmaddsub132pd1 : instruction :=
  definst "vfmaddsub132pd" $ do
    pattern fun (v_2629 : reg (bv 128)) (v_2630 : reg (bv 128)) (v_2631 : reg (bv 128)) => do
      v_5631 <- getRegister v_2631;
      v_5633 <- getRegister v_2630;
      v_5635 <- getRegister v_2629;
      v_5638 <- eval (extract v_5631 64 128);
      v_5646 <- eval (extract v_5635 64 128);
      v_5655 <- eval (extract v_5633 64 128);
      setRegister (lhs.of_reg v_2631) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_5631 0 64) (extract v_5633 0 64) (extract v_5635 0 64)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5638 0 1)) (uvalueMInt (extract v_5638 1 12)) (uvalueMInt (extract v_5638 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5646 0 1)) (uvalueMInt (extract v_5646 1 12)) (uvalueMInt (extract v_5646 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5655 0 1)) (uvalueMInt (extract v_5655 1 12)) (uvalueMInt (extract v_5655 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2640 : reg (bv 256)) (v_2641 : reg (bv 256)) (v_2642 : reg (bv 256)) => do
      v_5672 <- getRegister v_2642;
      v_5674 <- getRegister v_2641;
      v_5676 <- getRegister v_2640;
      v_5679 <- eval (extract v_5672 64 128);
      v_5687 <- eval (extract v_5676 64 128);
      v_5696 <- eval (extract v_5674 64 128);
      v_5711 <- eval (extract v_5672 192 256);
      v_5719 <- eval (extract v_5676 192 256);
      v_5728 <- eval (extract v_5674 192 256);
      setRegister (lhs.of_reg v_2642) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_5672 0 64) (extract v_5674 0 64) (extract v_5676 0 64)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5679 0 1)) (uvalueMInt (extract v_5679 1 12)) (uvalueMInt (extract v_5679 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5687 0 1)) (uvalueMInt (extract v_5687 1 12)) (uvalueMInt (extract v_5687 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5696 0 1)) (uvalueMInt (extract v_5696 1 12)) (uvalueMInt (extract v_5696 12 64)))) 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_5672 128 192) (extract v_5674 128 192) (extract v_5676 128 192)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5711 0 1)) (uvalueMInt (extract v_5711 1 12)) (uvalueMInt (extract v_5711 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5719 0 1)) (uvalueMInt (extract v_5719 1 12)) (uvalueMInt (extract v_5719 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5728 0 1)) (uvalueMInt (extract v_5728 1 12)) (uvalueMInt (extract v_5728 12 64)))) 64)));
      pure ()
    pat_end;
    pattern fun (v_2626 : Mem) (v_2624 : reg (bv 128)) (v_2625 : reg (bv 128)) => do
      v_16502 <- getRegister v_2625;
      v_16504 <- getRegister v_2624;
      v_16506 <- evaluateAddress v_2626;
      v_16507 <- load v_16506 16;
      v_16510 <- eval (extract v_16502 64 128);
      v_16518 <- eval (extract v_16507 64 128);
      v_16527 <- eval (extract v_16504 64 128);
      setRegister (lhs.of_reg v_2625) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_16502 0 64) (extract v_16504 0 64) (extract v_16507 0 64)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_16510 0 1)) (uvalueMInt (extract v_16510 1 12)) (uvalueMInt (extract v_16510 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_16518 0 1)) (uvalueMInt (extract v_16518 1 12)) (uvalueMInt (extract v_16518 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_16527 0 1)) (uvalueMInt (extract v_16527 1 12)) (uvalueMInt (extract v_16527 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2635 : Mem) (v_2636 : reg (bv 256)) (v_2637 : reg (bv 256)) => do
      v_16539 <- getRegister v_2637;
      v_16541 <- getRegister v_2636;
      v_16543 <- evaluateAddress v_2635;
      v_16544 <- load v_16543 32;
      v_16547 <- eval (extract v_16539 64 128);
      v_16555 <- eval (extract v_16544 64 128);
      v_16564 <- eval (extract v_16541 64 128);
      v_16579 <- eval (extract v_16539 192 256);
      v_16587 <- eval (extract v_16544 192 256);
      v_16596 <- eval (extract v_16541 192 256);
      setRegister (lhs.of_reg v_2637) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_16539 0 64) (extract v_16541 0 64) (extract v_16544 0 64)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_16547 0 1)) (uvalueMInt (extract v_16547 1 12)) (uvalueMInt (extract v_16547 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_16555 0 1)) (uvalueMInt (extract v_16555 1 12)) (uvalueMInt (extract v_16555 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_16564 0 1)) (uvalueMInt (extract v_16564 1 12)) (uvalueMInt (extract v_16564 12 64)))) 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_16539 128 192) (extract v_16541 128 192) (extract v_16544 128 192)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_16579 0 1)) (uvalueMInt (extract v_16579 1 12)) (uvalueMInt (extract v_16579 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_16587 0 1)) (uvalueMInt (extract v_16587 1 12)) (uvalueMInt (extract v_16587 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_16596 0 1)) (uvalueMInt (extract v_16596 1 12)) (uvalueMInt (extract v_16596 12 64)))) 64)));
      pure ()
    pat_end
