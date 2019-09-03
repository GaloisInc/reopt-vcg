def vrcpps1 : instruction :=
  definst "vrcpps" $ do
    pattern fun (v_2787 : reg (bv 128)) (v_2788 : reg (bv 128)) => do
      v_6509 <- getRegister v_2787;
      v_6510 <- eval (extract v_6509 0 32);
      v_6520 <- eval (extract v_6509 32 64);
      v_6530 <- eval (extract v_6509 64 96);
      v_6540 <- eval (extract v_6509 96 128);
      setRegister (lhs.of_reg v_2788) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6510 0 1)) (uvalueMInt (extract v_6510 1 9)) (uvalueMInt (extract v_6510 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6520 0 1)) (uvalueMInt (extract v_6520 1 9)) (uvalueMInt (extract v_6520 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6530 0 1)) (uvalueMInt (extract v_6530 1 9)) (uvalueMInt (extract v_6530 9 32)))) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6540 0 1)) (uvalueMInt (extract v_6540 1 9)) (uvalueMInt (extract v_6540 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_2796 : reg (bv 256)) (v_2797 : reg (bv 256)) => do
      v_6558 <- getRegister v_2796;
      v_6559 <- eval (extract v_6558 0 32);
      v_6569 <- eval (extract v_6558 32 64);
      v_6579 <- eval (extract v_6558 64 96);
      v_6589 <- eval (extract v_6558 96 128);
      v_6599 <- eval (extract v_6558 128 160);
      v_6609 <- eval (extract v_6558 160 192);
      v_6619 <- eval (extract v_6558 192 224);
      v_6629 <- eval (extract v_6558 224 256);
      setRegister (lhs.of_reg v_2797) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6559 0 1)) (uvalueMInt (extract v_6559 1 9)) (uvalueMInt (extract v_6559 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6569 0 1)) (uvalueMInt (extract v_6569 1 9)) (uvalueMInt (extract v_6569 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6579 0 1)) (uvalueMInt (extract v_6579 1 9)) (uvalueMInt (extract v_6579 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6589 0 1)) (uvalueMInt (extract v_6589 1 9)) (uvalueMInt (extract v_6589 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6599 0 1)) (uvalueMInt (extract v_6599 1 9)) (uvalueMInt (extract v_6599 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6609 0 1)) (uvalueMInt (extract v_6609 1 9)) (uvalueMInt (extract v_6609 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6619 0 1)) (uvalueMInt (extract v_6619 1 9)) (uvalueMInt (extract v_6619 9 32)))) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6629 0 1)) (uvalueMInt (extract v_6629 1 9)) (uvalueMInt (extract v_6629 9 32)))) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2783 : Mem) (v_2784 : reg (bv 128)) => do
      v_12901 <- evaluateAddress v_2783;
      v_12902 <- load v_12901 16;
      v_12903 <- eval (extract v_12902 0 32);
      v_12913 <- eval (extract v_12902 32 64);
      v_12923 <- eval (extract v_12902 64 96);
      v_12933 <- eval (extract v_12902 96 128);
      setRegister (lhs.of_reg v_2784) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12903 0 1)) (uvalueMInt (extract v_12903 1 9)) (uvalueMInt (extract v_12903 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12913 0 1)) (uvalueMInt (extract v_12913 1 9)) (uvalueMInt (extract v_12913 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12923 0 1)) (uvalueMInt (extract v_12923 1 9)) (uvalueMInt (extract v_12923 9 32)))) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12933 0 1)) (uvalueMInt (extract v_12933 1 9)) (uvalueMInt (extract v_12933 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_2792 : Mem) (v_2793 : reg (bv 256)) => do
      v_12947 <- evaluateAddress v_2792;
      v_12948 <- load v_12947 32;
      v_12949 <- eval (extract v_12948 0 32);
      v_12959 <- eval (extract v_12948 32 64);
      v_12969 <- eval (extract v_12948 64 96);
      v_12979 <- eval (extract v_12948 96 128);
      v_12989 <- eval (extract v_12948 128 160);
      v_12999 <- eval (extract v_12948 160 192);
      v_13009 <- eval (extract v_12948 192 224);
      v_13019 <- eval (extract v_12948 224 256);
      setRegister (lhs.of_reg v_2793) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12949 0 1)) (uvalueMInt (extract v_12949 1 9)) (uvalueMInt (extract v_12949 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12959 0 1)) (uvalueMInt (extract v_12959 1 9)) (uvalueMInt (extract v_12959 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12969 0 1)) (uvalueMInt (extract v_12969 1 9)) (uvalueMInt (extract v_12969 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12979 0 1)) (uvalueMInt (extract v_12979 1 9)) (uvalueMInt (extract v_12979 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12989 0 1)) (uvalueMInt (extract v_12989 1 9)) (uvalueMInt (extract v_12989 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12999 0 1)) (uvalueMInt (extract v_12999 1 9)) (uvalueMInt (extract v_12999 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_13009 0 1)) (uvalueMInt (extract v_13009 1 9)) (uvalueMInt (extract v_13009 9 32)))) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_13019 0 1)) (uvalueMInt (extract v_13019 1 9)) (uvalueMInt (extract v_13019 9 32)))) 32))))))));
      pure ()
    pat_end
