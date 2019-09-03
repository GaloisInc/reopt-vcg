def vdivss1 : instruction :=
  definst "vdivss" $ do
    pattern fun (v_3415 : reg (bv 128)) (v_3416 : reg (bv 128)) (v_3417 : reg (bv 128)) => do
      v_7512 <- getRegister v_3416;
      v_7514 <- eval (extract v_7512 96 128);
      v_7522 <- getRegister v_3415;
      v_7523 <- eval (extract v_7522 96 128);
      setRegister (lhs.of_reg v_3417) (concat (extract v_7512 0 96) (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7514 0 1)) (uvalueMInt (extract v_7514 1 9)) (uvalueMInt (extract v_7514 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7523 0 1)) (uvalueMInt (extract v_7523 1 9)) (uvalueMInt (extract v_7523 9 32)))) 32));
      pure ()
    pat_end;
    pattern fun (v_3407 : Mem) (v_3410 : reg (bv 128)) (v_3411 : reg (bv 128)) => do
      v_12710 <- getRegister v_3410;
      v_12712 <- eval (extract v_12710 96 128);
      v_12720 <- evaluateAddress v_3407;
      v_12721 <- load v_12720 4;
      setRegister (lhs.of_reg v_3411) (concat (extract v_12710 0 96) (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12712 0 1)) (uvalueMInt (extract v_12712 1 9)) (uvalueMInt (extract v_12712 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12721 0 1)) (uvalueMInt (extract v_12721 1 9)) (uvalueMInt (extract v_12721 9 32)))) 32));
      pure ()
    pat_end
