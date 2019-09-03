def mulps1 : instruction :=
  definst "mulps" $ do
    pattern fun (v_2749 : reg (bv 128)) (v_2750 : reg (bv 128)) => do
      v_4221 <- getRegister v_2750;
      v_4222 <- eval (extract v_4221 0 32);
      v_4230 <- getRegister v_2749;
      v_4231 <- eval (extract v_4230 0 32);
      v_4241 <- eval (extract v_4221 32 64);
      v_4249 <- eval (extract v_4230 32 64);
      v_4259 <- eval (extract v_4221 64 96);
      v_4267 <- eval (extract v_4230 64 96);
      v_4277 <- eval (extract v_4221 96 128);
      v_4285 <- eval (extract v_4230 96 128);
      setRegister (lhs.of_reg v_2750) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4222 0 1)) (uvalueMInt (extract v_4222 1 9)) (uvalueMInt (extract v_4222 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4231 0 1)) (uvalueMInt (extract v_4231 1 9)) (uvalueMInt (extract v_4231 9 32)))) 32) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4241 0 1)) (uvalueMInt (extract v_4241 1 9)) (uvalueMInt (extract v_4241 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4249 0 1)) (uvalueMInt (extract v_4249 1 9)) (uvalueMInt (extract v_4249 9 32)))) 32) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4259 0 1)) (uvalueMInt (extract v_4259 1 9)) (uvalueMInt (extract v_4259 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4267 0 1)) (uvalueMInt (extract v_4267 1 9)) (uvalueMInt (extract v_4267 9 32)))) 32) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4277 0 1)) (uvalueMInt (extract v_4277 1 9)) (uvalueMInt (extract v_4277 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4285 0 1)) (uvalueMInt (extract v_4285 1 9)) (uvalueMInt (extract v_4285 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_2745 : Mem) (v_2746 : reg (bv 128)) => do
      v_8975 <- getRegister v_2746;
      v_8976 <- eval (extract v_8975 0 32);
      v_8984 <- evaluateAddress v_2745;
      v_8985 <- load v_8984 16;
      v_8986 <- eval (extract v_8985 0 32);
      v_8996 <- eval (extract v_8975 32 64);
      v_9004 <- eval (extract v_8985 32 64);
      v_9014 <- eval (extract v_8975 64 96);
      v_9022 <- eval (extract v_8985 64 96);
      v_9032 <- eval (extract v_8975 96 128);
      v_9040 <- eval (extract v_8985 96 128);
      setRegister (lhs.of_reg v_2746) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8976 0 1)) (uvalueMInt (extract v_8976 1 9)) (uvalueMInt (extract v_8976 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8986 0 1)) (uvalueMInt (extract v_8986 1 9)) (uvalueMInt (extract v_8986 9 32)))) 32) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8996 0 1)) (uvalueMInt (extract v_8996 1 9)) (uvalueMInt (extract v_8996 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9004 0 1)) (uvalueMInt (extract v_9004 1 9)) (uvalueMInt (extract v_9004 9 32)))) 32) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9014 0 1)) (uvalueMInt (extract v_9014 1 9)) (uvalueMInt (extract v_9014 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9022 0 1)) (uvalueMInt (extract v_9022 1 9)) (uvalueMInt (extract v_9022 9 32)))) 32) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9032 0 1)) (uvalueMInt (extract v_9032 1 9)) (uvalueMInt (extract v_9032 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9040 0 1)) (uvalueMInt (extract v_9040 1 9)) (uvalueMInt (extract v_9040 9 32)))) 32))));
      pure ()
    pat_end
