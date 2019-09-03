def divsd1 : instruction :=
  definst "divsd" $ do
    pattern fun (v_2763 : reg (bv 128)) (v_2764 : reg (bv 128)) => do
      v_4692 <- getRegister v_2764;
      v_4694 <- eval (extract v_4692 64 128);
      v_4702 <- getRegister v_2763;
      v_4703 <- eval (extract v_4702 64 128);
      setRegister (lhs.of_reg v_2764) (concat (extract v_4692 0 64) (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4694 0 1)) (uvalueMInt (extract v_4694 1 12)) (uvalueMInt (extract v_4694 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4703 0 1)) (uvalueMInt (extract v_4703 1 12)) (uvalueMInt (extract v_4703 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2757 : Mem) (v_2759 : reg (bv 128)) => do
      v_8717 <- getRegister v_2759;
      v_8719 <- eval (extract v_8717 64 128);
      v_8727 <- evaluateAddress v_2757;
      v_8728 <- load v_8727 8;
      setRegister (lhs.of_reg v_2759) (concat (extract v_8717 0 64) (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8719 0 1)) (uvalueMInt (extract v_8719 1 12)) (uvalueMInt (extract v_8719 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8728 0 1)) (uvalueMInt (extract v_8728 1 12)) (uvalueMInt (extract v_8728 12 64)))) 64));
      pure ()
    pat_end
