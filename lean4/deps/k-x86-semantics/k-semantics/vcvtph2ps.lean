def vcvtph2ps1 : instruction :=
  definst "vcvtph2ps" $ do
    pattern fun (v_3083 : reg (bv 128)) (v_3084 : reg (bv 128)) => do
      v_6461 <- getRegister v_3083;
      v_6462 <- eval (extract v_6461 64 80);
      v_6472 <- eval (extract v_6461 80 96);
      v_6482 <- eval (extract v_6461 96 112);
      v_6492 <- eval (extract v_6461 112 128);
      setRegister (lhs.of_reg v_3084) (concat (Float2MInt (roundFloat (MIntToFloatImpl 11 5 (uvalueMInt (extract v_6462 0 1)) (uvalueMInt (extract v_6462 1 6)) (uvalueMInt (extract v_6462 6 16))) 24 8) 32) (concat (Float2MInt (roundFloat (MIntToFloatImpl 11 5 (uvalueMInt (extract v_6472 0 1)) (uvalueMInt (extract v_6472 1 6)) (uvalueMInt (extract v_6472 6 16))) 24 8) 32) (concat (Float2MInt (roundFloat (MIntToFloatImpl 11 5 (uvalueMInt (extract v_6482 0 1)) (uvalueMInt (extract v_6482 1 6)) (uvalueMInt (extract v_6482 6 16))) 24 8) 32) (Float2MInt (roundFloat (MIntToFloatImpl 11 5 (uvalueMInt (extract v_6492 0 1)) (uvalueMInt (extract v_6492 1 6)) (uvalueMInt (extract v_6492 6 16))) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_3093 : reg (bv 128)) (v_3089 : reg (bv 256)) => do
      v_6510 <- getRegister v_3093;
      v_6511 <- eval (extract v_6510 0 16);
      v_6521 <- eval (extract v_6510 16 32);
      v_6531 <- eval (extract v_6510 32 48);
      v_6541 <- eval (extract v_6510 48 64);
      v_6551 <- eval (extract v_6510 64 80);
      v_6561 <- eval (extract v_6510 80 96);
      v_6571 <- eval (extract v_6510 96 112);
      v_6581 <- eval (extract v_6510 112 128);
      setRegister (lhs.of_reg v_3089) (concat (Float2MInt (roundFloat (MIntToFloatImpl 11 5 (uvalueMInt (extract v_6511 0 1)) (uvalueMInt (extract v_6511 1 6)) (uvalueMInt (extract v_6511 6 16))) 24 8) 32) (concat (Float2MInt (roundFloat (MIntToFloatImpl 11 5 (uvalueMInt (extract v_6521 0 1)) (uvalueMInt (extract v_6521 1 6)) (uvalueMInt (extract v_6521 6 16))) 24 8) 32) (concat (Float2MInt (roundFloat (MIntToFloatImpl 11 5 (uvalueMInt (extract v_6531 0 1)) (uvalueMInt (extract v_6531 1 6)) (uvalueMInt (extract v_6531 6 16))) 24 8) 32) (concat (Float2MInt (roundFloat (MIntToFloatImpl 11 5 (uvalueMInt (extract v_6541 0 1)) (uvalueMInt (extract v_6541 1 6)) (uvalueMInt (extract v_6541 6 16))) 24 8) 32) (concat (Float2MInt (roundFloat (MIntToFloatImpl 11 5 (uvalueMInt (extract v_6551 0 1)) (uvalueMInt (extract v_6551 1 6)) (uvalueMInt (extract v_6551 6 16))) 24 8) 32) (concat (Float2MInt (roundFloat (MIntToFloatImpl 11 5 (uvalueMInt (extract v_6561 0 1)) (uvalueMInt (extract v_6561 1 6)) (uvalueMInt (extract v_6561 6 16))) 24 8) 32) (concat (Float2MInt (roundFloat (MIntToFloatImpl 11 5 (uvalueMInt (extract v_6571 0 1)) (uvalueMInt (extract v_6571 1 6)) (uvalueMInt (extract v_6571 6 16))) 24 8) 32) (Float2MInt (roundFloat (MIntToFloatImpl 11 5 (uvalueMInt (extract v_6581 0 1)) (uvalueMInt (extract v_6581 1 6)) (uvalueMInt (extract v_6581 6 16))) 24 8) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3076 : Mem) (v_3079 : reg (bv 128)) => do
      v_11899 <- evaluateAddress v_3076;
      v_11900 <- load v_11899 8;
      v_11901 <- eval (extract v_11900 0 16);
      v_11911 <- eval (extract v_11900 16 32);
      v_11921 <- eval (extract v_11900 32 48);
      v_11931 <- eval (extract v_11900 48 64);
      setRegister (lhs.of_reg v_3079) (concat (Float2MInt (roundFloat (MIntToFloatImpl 11 5 (uvalueMInt (extract v_11901 0 1)) (uvalueMInt (extract v_11901 1 6)) (uvalueMInt (extract v_11901 6 16))) 24 8) 32) (concat (Float2MInt (roundFloat (MIntToFloatImpl 11 5 (uvalueMInt (extract v_11911 0 1)) (uvalueMInt (extract v_11911 1 6)) (uvalueMInt (extract v_11911 6 16))) 24 8) 32) (concat (Float2MInt (roundFloat (MIntToFloatImpl 11 5 (uvalueMInt (extract v_11921 0 1)) (uvalueMInt (extract v_11921 1 6)) (uvalueMInt (extract v_11921 6 16))) 24 8) 32) (Float2MInt (roundFloat (MIntToFloatImpl 11 5 (uvalueMInt (extract v_11931 0 1)) (uvalueMInt (extract v_11931 1 6)) (uvalueMInt (extract v_11931 6 16))) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_3085 : Mem) (v_3086 : reg (bv 256)) => do
      v_11945 <- evaluateAddress v_3085;
      v_11946 <- load v_11945 16;
      v_11947 <- eval (extract v_11946 0 16);
      v_11957 <- eval (extract v_11946 16 32);
      v_11967 <- eval (extract v_11946 32 48);
      v_11977 <- eval (extract v_11946 48 64);
      v_11987 <- eval (extract v_11946 64 80);
      v_11997 <- eval (extract v_11946 80 96);
      v_12007 <- eval (extract v_11946 96 112);
      v_12017 <- eval (extract v_11946 112 128);
      setRegister (lhs.of_reg v_3086) (concat (Float2MInt (roundFloat (MIntToFloatImpl 11 5 (uvalueMInt (extract v_11947 0 1)) (uvalueMInt (extract v_11947 1 6)) (uvalueMInt (extract v_11947 6 16))) 24 8) 32) (concat (Float2MInt (roundFloat (MIntToFloatImpl 11 5 (uvalueMInt (extract v_11957 0 1)) (uvalueMInt (extract v_11957 1 6)) (uvalueMInt (extract v_11957 6 16))) 24 8) 32) (concat (Float2MInt (roundFloat (MIntToFloatImpl 11 5 (uvalueMInt (extract v_11967 0 1)) (uvalueMInt (extract v_11967 1 6)) (uvalueMInt (extract v_11967 6 16))) 24 8) 32) (concat (Float2MInt (roundFloat (MIntToFloatImpl 11 5 (uvalueMInt (extract v_11977 0 1)) (uvalueMInt (extract v_11977 1 6)) (uvalueMInt (extract v_11977 6 16))) 24 8) 32) (concat (Float2MInt (roundFloat (MIntToFloatImpl 11 5 (uvalueMInt (extract v_11987 0 1)) (uvalueMInt (extract v_11987 1 6)) (uvalueMInt (extract v_11987 6 16))) 24 8) 32) (concat (Float2MInt (roundFloat (MIntToFloatImpl 11 5 (uvalueMInt (extract v_11997 0 1)) (uvalueMInt (extract v_11997 1 6)) (uvalueMInt (extract v_11997 6 16))) 24 8) 32) (concat (Float2MInt (roundFloat (MIntToFloatImpl 11 5 (uvalueMInt (extract v_12007 0 1)) (uvalueMInt (extract v_12007 1 6)) (uvalueMInt (extract v_12007 6 16))) 24 8) 32) (Float2MInt (roundFloat (MIntToFloatImpl 11 5 (uvalueMInt (extract v_12017 0 1)) (uvalueMInt (extract v_12017 1 6)) (uvalueMInt (extract v_12017 6 16))) 24 8) 32))))))));
      pure ()
    pat_end
