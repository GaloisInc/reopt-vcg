def divpd1 : instruction :=
  definst "divpd" $ do
    pattern fun (v_2738 : reg (bv 128)) (v_2739 : reg (bv 128)) => do
      v_4549 <- getRegister v_2739;
      v_4550 <- eval (extract v_4549 0 64);
      v_4558 <- getRegister v_2738;
      v_4559 <- eval (extract v_4558 0 64);
      v_4569 <- eval (extract v_4549 64 128);
      v_4577 <- eval (extract v_4558 64 128);
      setRegister (lhs.of_reg v_2739) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4550 0 1)) (uvalueMInt (extract v_4550 1 12)) (uvalueMInt (extract v_4550 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4559 0 1)) (uvalueMInt (extract v_4559 1 12)) (uvalueMInt (extract v_4559 12 64)))) 64) (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4569 0 1)) (uvalueMInt (extract v_4569 1 12)) (uvalueMInt (extract v_4569 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4577 0 1)) (uvalueMInt (extract v_4577 1 12)) (uvalueMInt (extract v_4577 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2732 : Mem) (v_2734 : reg (bv 128)) => do
      v_8582 <- getRegister v_2734;
      v_8583 <- eval (extract v_8582 0 64);
      v_8591 <- evaluateAddress v_2732;
      v_8592 <- load v_8591 16;
      v_8593 <- eval (extract v_8592 0 64);
      v_8603 <- eval (extract v_8582 64 128);
      v_8611 <- eval (extract v_8592 64 128);
      setRegister (lhs.of_reg v_2734) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8583 0 1)) (uvalueMInt (extract v_8583 1 12)) (uvalueMInt (extract v_8583 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8593 0 1)) (uvalueMInt (extract v_8593 1 12)) (uvalueMInt (extract v_8593 12 64)))) 64) (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8603 0 1)) (uvalueMInt (extract v_8603 1 12)) (uvalueMInt (extract v_8603 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8611 0 1)) (uvalueMInt (extract v_8611 1 12)) (uvalueMInt (extract v_8611 12 64)))) 64));
      pure ()
    pat_end
