def addsubps1 : instruction :=
  definst "addsubps" $ do
    pattern fun (v_2681 : reg (bv 128)) (v_2682 : reg (bv 128)) => do
      v_5097 <- getRegister v_2682;
      v_5098 <- eval (extract v_5097 0 32);
      v_5106 <- getRegister v_2681;
      v_5107 <- eval (extract v_5106 0 32);
      v_5117 <- eval (extract v_5097 32 64);
      v_5125 <- eval (extract v_5106 32 64);
      v_5136 <- eval (extract v_5097 64 96);
      v_5144 <- eval (extract v_5106 64 96);
      v_5154 <- eval (extract v_5097 96 128);
      v_5162 <- eval (extract v_5106 96 128);
      setRegister (lhs.of_reg v_2682) (concat (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5098 0 1)) (uvalueMInt (extract v_5098 1 9)) (uvalueMInt (extract v_5098 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5107 0 1)) (uvalueMInt (extract v_5107 1 9)) (uvalueMInt (extract v_5107 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5117 0 1)) (uvalueMInt (extract v_5117 1 9)) (uvalueMInt (extract v_5117 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5125 0 1)) (uvalueMInt (extract v_5125 1 9)) (uvalueMInt (extract v_5125 9 32)))) 32)) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5136 0 1)) (uvalueMInt (extract v_5136 1 9)) (uvalueMInt (extract v_5136 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5144 0 1)) (uvalueMInt (extract v_5144 1 9)) (uvalueMInt (extract v_5144 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5154 0 1)) (uvalueMInt (extract v_5154 1 9)) (uvalueMInt (extract v_5154 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5162 0 1)) (uvalueMInt (extract v_5162 1 9)) (uvalueMInt (extract v_5162 9 32)))) 32)));
      pure ()
    pat_end;
    pattern fun (v_2676 : Mem) (v_2677 : reg (bv 128)) => do
      v_9483 <- getRegister v_2677;
      v_9484 <- eval (extract v_9483 0 32);
      v_9492 <- evaluateAddress v_2676;
      v_9493 <- load v_9492 16;
      v_9494 <- eval (extract v_9493 0 32);
      v_9504 <- eval (extract v_9483 32 64);
      v_9512 <- eval (extract v_9493 32 64);
      v_9523 <- eval (extract v_9483 64 96);
      v_9531 <- eval (extract v_9493 64 96);
      v_9541 <- eval (extract v_9483 96 128);
      v_9549 <- eval (extract v_9493 96 128);
      setRegister (lhs.of_reg v_2677) (concat (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9484 0 1)) (uvalueMInt (extract v_9484 1 9)) (uvalueMInt (extract v_9484 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9494 0 1)) (uvalueMInt (extract v_9494 1 9)) (uvalueMInt (extract v_9494 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9504 0 1)) (uvalueMInt (extract v_9504 1 9)) (uvalueMInt (extract v_9504 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9512 0 1)) (uvalueMInt (extract v_9512 1 9)) (uvalueMInt (extract v_9512 9 32)))) 32)) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9523 0 1)) (uvalueMInt (extract v_9523 1 9)) (uvalueMInt (extract v_9523 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9531 0 1)) (uvalueMInt (extract v_9531 1 9)) (uvalueMInt (extract v_9531 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9541 0 1)) (uvalueMInt (extract v_9541 1 9)) (uvalueMInt (extract v_9541 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9549 0 1)) (uvalueMInt (extract v_9549 1 9)) (uvalueMInt (extract v_9549 9 32)))) 32)));
      pure ()
    pat_end
