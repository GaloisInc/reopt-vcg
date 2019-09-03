def cvtpd2ps1 : instruction :=
  definst "cvtpd2ps" $ do
    pattern fun (v_2503 : reg (bv 128)) (v_2504 : reg (bv 128)) => do
      v_4109 <- getRegister v_2503;
      v_4110 <- eval (extract v_4109 0 64);
      v_4120 <- eval (extract v_4109 64 128);
      setRegister (lhs.of_reg v_2504) (concat (expression.bv_nat 64 0) (concat (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4110 0 1)) (uvalueMInt (extract v_4110 1 12)) (uvalueMInt (extract v_4110 12 64))) 24 8) 32) (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4120 0 1)) (uvalueMInt (extract v_4120 1 12)) (uvalueMInt (extract v_4120 12 64))) 24 8) 32)));
      pure ()
    pat_end;
    pattern fun (v_2497 : Mem) (v_2499 : reg (bv 128)) => do
      v_8334 <- evaluateAddress v_2497;
      v_8335 <- load v_8334 16;
      v_8336 <- eval (extract v_8335 0 64);
      v_8346 <- eval (extract v_8335 64 128);
      setRegister (lhs.of_reg v_2499) (concat (expression.bv_nat 64 0) (concat (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8336 0 1)) (uvalueMInt (extract v_8336 1 12)) (uvalueMInt (extract v_8336 12 64))) 24 8) 32) (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8346 0 1)) (uvalueMInt (extract v_8346 1 12)) (uvalueMInt (extract v_8346 12 64))) 24 8) 32)));
      pure ()
    pat_end
