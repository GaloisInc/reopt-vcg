def divps1 : instruction :=
  definst "divps" $ do
    pattern fun (v_2747 : reg (bv 128)) (v_2748 : reg (bv 128)) => do
      v_4593 <- getRegister v_2748;
      v_4594 <- eval (extract v_4593 0 32);
      v_4602 <- getRegister v_2747;
      v_4603 <- eval (extract v_4602 0 32);
      v_4613 <- eval (extract v_4593 32 64);
      v_4621 <- eval (extract v_4602 32 64);
      v_4631 <- eval (extract v_4593 64 96);
      v_4639 <- eval (extract v_4602 64 96);
      v_4649 <- eval (extract v_4593 96 128);
      v_4657 <- eval (extract v_4602 96 128);
      setRegister (lhs.of_reg v_2748) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4594 0 1)) (uvalueMInt (extract v_4594 1 9)) (uvalueMInt (extract v_4594 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4603 0 1)) (uvalueMInt (extract v_4603 1 9)) (uvalueMInt (extract v_4603 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4613 0 1)) (uvalueMInt (extract v_4613 1 9)) (uvalueMInt (extract v_4613 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4621 0 1)) (uvalueMInt (extract v_4621 1 9)) (uvalueMInt (extract v_4621 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4631 0 1)) (uvalueMInt (extract v_4631 1 9)) (uvalueMInt (extract v_4631 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4639 0 1)) (uvalueMInt (extract v_4639 1 9)) (uvalueMInt (extract v_4639 9 32)))) 32) (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4649 0 1)) (uvalueMInt (extract v_4649 1 9)) (uvalueMInt (extract v_4649 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4657 0 1)) (uvalueMInt (extract v_4657 1 9)) (uvalueMInt (extract v_4657 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_2741 : Mem) (v_2743 : reg (bv 128)) => do
      v_8623 <- getRegister v_2743;
      v_8624 <- eval (extract v_8623 0 32);
      v_8632 <- evaluateAddress v_2741;
      v_8633 <- load v_8632 16;
      v_8634 <- eval (extract v_8633 0 32);
      v_8644 <- eval (extract v_8623 32 64);
      v_8652 <- eval (extract v_8633 32 64);
      v_8662 <- eval (extract v_8623 64 96);
      v_8670 <- eval (extract v_8633 64 96);
      v_8680 <- eval (extract v_8623 96 128);
      v_8688 <- eval (extract v_8633 96 128);
      setRegister (lhs.of_reg v_2743) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8624 0 1)) (uvalueMInt (extract v_8624 1 9)) (uvalueMInt (extract v_8624 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8634 0 1)) (uvalueMInt (extract v_8634 1 9)) (uvalueMInt (extract v_8634 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8644 0 1)) (uvalueMInt (extract v_8644 1 9)) (uvalueMInt (extract v_8644 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8652 0 1)) (uvalueMInt (extract v_8652 1 9)) (uvalueMInt (extract v_8652 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8662 0 1)) (uvalueMInt (extract v_8662 1 9)) (uvalueMInt (extract v_8662 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8670 0 1)) (uvalueMInt (extract v_8670 1 9)) (uvalueMInt (extract v_8670 9 32)))) 32) (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8680 0 1)) (uvalueMInt (extract v_8680 1 9)) (uvalueMInt (extract v_8680 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8688 0 1)) (uvalueMInt (extract v_8688 1 9)) (uvalueMInt (extract v_8688 9 32)))) 32))));
      pure ()
    pat_end
