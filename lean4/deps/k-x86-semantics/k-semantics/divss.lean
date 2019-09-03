def divss1 : instruction :=
  definst "divss" $ do
    pattern fun (v_2772 : reg (bv 128)) (v_2773 : reg (bv 128)) => do
      v_4719 <- getRegister v_2773;
      v_4721 <- eval (extract v_4719 96 128);
      v_4729 <- getRegister v_2772;
      v_4730 <- eval (extract v_4729 96 128);
      setRegister (lhs.of_reg v_2773) (concat (extract v_4719 0 96) (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4721 0 1)) (uvalueMInt (extract v_4721 1 9)) (uvalueMInt (extract v_4721 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4730 0 1)) (uvalueMInt (extract v_4730 1 9)) (uvalueMInt (extract v_4730 9 32)))) 32));
      pure ()
    pat_end;
    pattern fun (v_2766 : Mem) (v_2768 : reg (bv 128)) => do
      v_8740 <- getRegister v_2768;
      v_8742 <- eval (extract v_8740 96 128);
      v_8750 <- evaluateAddress v_2766;
      v_8751 <- load v_8750 4;
      setRegister (lhs.of_reg v_2768) (concat (extract v_8740 0 96) (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8742 0 1)) (uvalueMInt (extract v_8742 1 9)) (uvalueMInt (extract v_8742 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8751 0 1)) (uvalueMInt (extract v_8751 1 9)) (uvalueMInt (extract v_8751 9 32)))) 32));
      pure ()
    pat_end
