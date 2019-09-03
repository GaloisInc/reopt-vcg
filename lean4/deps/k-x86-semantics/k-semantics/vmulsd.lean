def vmulsd1 : instruction :=
  definst "vmulsd" $ do
    pattern fun (v_3126 : reg (bv 128)) (v_3127 : reg (bv 128)) (v_3128 : reg (bv 128)) => do
      v_5839 <- getRegister v_3127;
      v_5841 <- eval (extract v_5839 64 128);
      v_5849 <- getRegister v_3126;
      v_5850 <- eval (extract v_5849 64 128);
      setRegister (lhs.of_reg v_3128) (concat (extract v_5839 0 64) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5841 0 1)) (uvalueMInt (extract v_5841 1 12)) (uvalueMInt (extract v_5841 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5850 0 1)) (uvalueMInt (extract v_5850 1 12)) (uvalueMInt (extract v_5850 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_3121 : Mem) (v_3122 : reg (bv 128)) (v_3123 : reg (bv 128)) => do
      v_11579 <- getRegister v_3122;
      v_11581 <- eval (extract v_11579 64 128);
      v_11589 <- evaluateAddress v_3121;
      v_11590 <- load v_11589 8;
      setRegister (lhs.of_reg v_3123) (concat (extract v_11579 0 64) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11581 0 1)) (uvalueMInt (extract v_11581 1 12)) (uvalueMInt (extract v_11581 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11590 0 1)) (uvalueMInt (extract v_11590 1 12)) (uvalueMInt (extract v_11590 12 64)))) 64));
      pure ()
    pat_end
