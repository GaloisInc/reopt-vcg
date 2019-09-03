def addpd1 : instruction :=
  definst "addpd" $ do
    pattern fun (v_2610 : reg (bv 128)) (v_2611 : reg (bv 128)) => do
      v_4761 <- getRegister v_2611;
      v_4762 <- eval (extract v_4761 0 64);
      v_4770 <- getRegister v_2610;
      v_4771 <- eval (extract v_4770 0 64);
      v_4781 <- eval (extract v_4761 64 128);
      v_4789 <- eval (extract v_4770 64 128);
      setRegister (lhs.of_reg v_2611) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4762 0 1)) (uvalueMInt (extract v_4762 1 12)) (uvalueMInt (extract v_4762 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4771 0 1)) (uvalueMInt (extract v_4771 1 12)) (uvalueMInt (extract v_4771 12 64)))) 64) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4781 0 1)) (uvalueMInt (extract v_4781 1 12)) (uvalueMInt (extract v_4781 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4789 0 1)) (uvalueMInt (extract v_4789 1 12)) (uvalueMInt (extract v_4789 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2605 : Mem) (v_2606 : reg (bv 128)) => do
      v_9241 <- getRegister v_2606;
      v_9242 <- eval (extract v_9241 0 64);
      v_9250 <- evaluateAddress v_2605;
      v_9251 <- load v_9250 16;
      v_9252 <- eval (extract v_9251 0 64);
      v_9262 <- eval (extract v_9241 64 128);
      v_9270 <- eval (extract v_9251 64 128);
      setRegister (lhs.of_reg v_2606) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9242 0 1)) (uvalueMInt (extract v_9242 1 12)) (uvalueMInt (extract v_9242 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9252 0 1)) (uvalueMInt (extract v_9252 1 12)) (uvalueMInt (extract v_9252 12 64)))) 64) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9262 0 1)) (uvalueMInt (extract v_9262 1 12)) (uvalueMInt (extract v_9262 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9270 0 1)) (uvalueMInt (extract v_9270 1 12)) (uvalueMInt (extract v_9270 12 64)))) 64));
      pure ()
    pat_end
