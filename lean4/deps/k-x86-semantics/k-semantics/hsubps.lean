def hsubps1 : instruction :=
  definst "hsubps" $ do
    pattern fun (v_2854 : reg (bv 128)) (v_2855 : reg (bv 128)) => do
      v_5147 <- getRegister v_2854;
      v_5148 <- eval (extract v_5147 32 64);
      v_5156 <- eval (extract v_5147 0 32);
      v_5166 <- eval (extract v_5147 96 128);
      v_5174 <- eval (extract v_5147 64 96);
      v_5185 <- getRegister v_2855;
      v_5186 <- eval (extract v_5185 32 64);
      v_5194 <- eval (extract v_5185 0 32);
      v_5205 <- eval (extract v_5185 96 128);
      v_5213 <- eval (extract v_5185 64 96);
      setRegister (lhs.of_reg v_2855) (concat (concat (concat (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5148 0 1)) (uvalueMInt (extract v_5148 1 9)) (uvalueMInt (extract v_5148 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5156 0 1)) (uvalueMInt (extract v_5156 1 9)) (uvalueMInt (extract v_5156 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5166 0 1)) (uvalueMInt (extract v_5166 1 9)) (uvalueMInt (extract v_5166 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5174 0 1)) (uvalueMInt (extract v_5174 1 9)) (uvalueMInt (extract v_5174 9 32)))) 32)) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5186 0 1)) (uvalueMInt (extract v_5186 1 9)) (uvalueMInt (extract v_5186 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5194 0 1)) (uvalueMInt (extract v_5194 1 9)) (uvalueMInt (extract v_5194 9 32)))) 32)) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5205 0 1)) (uvalueMInt (extract v_5205 1 9)) (uvalueMInt (extract v_5205 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5213 0 1)) (uvalueMInt (extract v_5213 1 9)) (uvalueMInt (extract v_5213 9 32)))) 32));
      pure ()
    pat_end;
    pattern fun (v_2848 : Mem) (v_2850 : reg (bv 128)) => do
      v_9120 <- evaluateAddress v_2848;
      v_9121 <- load v_9120 16;
      v_9122 <- eval (extract v_9121 32 64);
      v_9130 <- eval (extract v_9121 0 32);
      v_9140 <- eval (extract v_9121 96 128);
      v_9148 <- eval (extract v_9121 64 96);
      v_9159 <- getRegister v_2850;
      v_9160 <- eval (extract v_9159 32 64);
      v_9168 <- eval (extract v_9159 0 32);
      v_9179 <- eval (extract v_9159 96 128);
      v_9187 <- eval (extract v_9159 64 96);
      setRegister (lhs.of_reg v_2850) (concat (concat (concat (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9122 0 1)) (uvalueMInt (extract v_9122 1 9)) (uvalueMInt (extract v_9122 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9130 0 1)) (uvalueMInt (extract v_9130 1 9)) (uvalueMInt (extract v_9130 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9140 0 1)) (uvalueMInt (extract v_9140 1 9)) (uvalueMInt (extract v_9140 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9148 0 1)) (uvalueMInt (extract v_9148 1 9)) (uvalueMInt (extract v_9148 9 32)))) 32)) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9160 0 1)) (uvalueMInt (extract v_9160 1 9)) (uvalueMInt (extract v_9160 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9168 0 1)) (uvalueMInt (extract v_9168 1 9)) (uvalueMInt (extract v_9168 9 32)))) 32)) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9179 0 1)) (uvalueMInt (extract v_9179 1 9)) (uvalueMInt (extract v_9179 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9187 0 1)) (uvalueMInt (extract v_9187 1 9)) (uvalueMInt (extract v_9187 9 32)))) 32));
      pure ()
    pat_end
