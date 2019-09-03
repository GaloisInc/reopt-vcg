def haddps1 : instruction :=
  definst "haddps" $ do
    pattern fun (v_2836 : reg (bv 128)) (v_2837 : reg (bv 128)) => do
      v_5021 <- getRegister v_2836;
      v_5022 <- eval (extract v_5021 32 64);
      v_5030 <- eval (extract v_5021 0 32);
      v_5040 <- eval (extract v_5021 96 128);
      v_5048 <- eval (extract v_5021 64 96);
      v_5059 <- getRegister v_2837;
      v_5060 <- eval (extract v_5059 32 64);
      v_5068 <- eval (extract v_5059 0 32);
      v_5079 <- eval (extract v_5059 96 128);
      v_5087 <- eval (extract v_5059 64 96);
      setRegister (lhs.of_reg v_2837) (concat (concat (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5022 0 1)) (uvalueMInt (extract v_5022 1 9)) (uvalueMInt (extract v_5022 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5030 0 1)) (uvalueMInt (extract v_5030 1 9)) (uvalueMInt (extract v_5030 9 32)))) 32) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5040 0 1)) (uvalueMInt (extract v_5040 1 9)) (uvalueMInt (extract v_5040 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5048 0 1)) (uvalueMInt (extract v_5048 1 9)) (uvalueMInt (extract v_5048 9 32)))) 32)) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5060 0 1)) (uvalueMInt (extract v_5060 1 9)) (uvalueMInt (extract v_5060 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5068 0 1)) (uvalueMInt (extract v_5068 1 9)) (uvalueMInt (extract v_5068 9 32)))) 32)) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5079 0 1)) (uvalueMInt (extract v_5079 1 9)) (uvalueMInt (extract v_5079 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5087 0 1)) (uvalueMInt (extract v_5087 1 9)) (uvalueMInt (extract v_5087 9 32)))) 32));
      pure ()
    pat_end;
    pattern fun (v_2830 : Mem) (v_2832 : reg (bv 128)) => do
      v_9000 <- evaluateAddress v_2830;
      v_9001 <- load v_9000 16;
      v_9002 <- eval (extract v_9001 32 64);
      v_9010 <- eval (extract v_9001 0 32);
      v_9020 <- eval (extract v_9001 96 128);
      v_9028 <- eval (extract v_9001 64 96);
      v_9039 <- getRegister v_2832;
      v_9040 <- eval (extract v_9039 32 64);
      v_9048 <- eval (extract v_9039 0 32);
      v_9059 <- eval (extract v_9039 96 128);
      v_9067 <- eval (extract v_9039 64 96);
      setRegister (lhs.of_reg v_2832) (concat (concat (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9002 0 1)) (uvalueMInt (extract v_9002 1 9)) (uvalueMInt (extract v_9002 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9010 0 1)) (uvalueMInt (extract v_9010 1 9)) (uvalueMInt (extract v_9010 9 32)))) 32) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9020 0 1)) (uvalueMInt (extract v_9020 1 9)) (uvalueMInt (extract v_9020 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9028 0 1)) (uvalueMInt (extract v_9028 1 9)) (uvalueMInt (extract v_9028 9 32)))) 32)) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9040 0 1)) (uvalueMInt (extract v_9040 1 9)) (uvalueMInt (extract v_9040 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9048 0 1)) (uvalueMInt (extract v_9048 1 9)) (uvalueMInt (extract v_9048 9 32)))) 32)) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9059 0 1)) (uvalueMInt (extract v_9059 1 9)) (uvalueMInt (extract v_9059 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9067 0 1)) (uvalueMInt (extract v_9067 1 9)) (uvalueMInt (extract v_9067 9 32)))) 32));
      pure ()
    pat_end
