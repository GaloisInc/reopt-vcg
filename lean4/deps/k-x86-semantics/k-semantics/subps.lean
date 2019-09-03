def subps1 : instruction :=
  definst "subps" $ do
    pattern fun (v_3201 : reg (bv 128)) (v_3202 : reg (bv 128)) => do
      v_7231 <- getRegister v_3202;
      v_7232 <- eval (extract v_7231 0 32);
      v_7240 <- getRegister v_3201;
      v_7241 <- eval (extract v_7240 0 32);
      v_7251 <- eval (extract v_7231 32 64);
      v_7259 <- eval (extract v_7240 32 64);
      v_7269 <- eval (extract v_7231 64 96);
      v_7277 <- eval (extract v_7240 64 96);
      v_7287 <- eval (extract v_7231 96 128);
      v_7295 <- eval (extract v_7240 96 128);
      setRegister (lhs.of_reg v_3202) (concat (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7232 0 1)) (uvalueMInt (extract v_7232 1 9)) (uvalueMInt (extract v_7232 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7241 0 1)) (uvalueMInt (extract v_7241 1 9)) (uvalueMInt (extract v_7241 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7251 0 1)) (uvalueMInt (extract v_7251 1 9)) (uvalueMInt (extract v_7251 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7259 0 1)) (uvalueMInt (extract v_7259 1 9)) (uvalueMInt (extract v_7259 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7269 0 1)) (uvalueMInt (extract v_7269 1 9)) (uvalueMInt (extract v_7269 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7277 0 1)) (uvalueMInt (extract v_7277 1 9)) (uvalueMInt (extract v_7277 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7287 0 1)) (uvalueMInt (extract v_7287 1 9)) (uvalueMInt (extract v_7287 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7295 0 1)) (uvalueMInt (extract v_7295 1 9)) (uvalueMInt (extract v_7295 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_3196 : Mem) (v_3197 : reg (bv 128)) => do
      v_10468 <- getRegister v_3197;
      v_10469 <- eval (extract v_10468 0 32);
      v_10477 <- evaluateAddress v_3196;
      v_10478 <- load v_10477 16;
      v_10479 <- eval (extract v_10478 0 32);
      v_10489 <- eval (extract v_10468 32 64);
      v_10497 <- eval (extract v_10478 32 64);
      v_10507 <- eval (extract v_10468 64 96);
      v_10515 <- eval (extract v_10478 64 96);
      v_10525 <- eval (extract v_10468 96 128);
      v_10533 <- eval (extract v_10478 96 128);
      setRegister (lhs.of_reg v_3197) (concat (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10469 0 1)) (uvalueMInt (extract v_10469 1 9)) (uvalueMInt (extract v_10469 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10479 0 1)) (uvalueMInt (extract v_10479 1 9)) (uvalueMInt (extract v_10479 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10489 0 1)) (uvalueMInt (extract v_10489 1 9)) (uvalueMInt (extract v_10489 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10497 0 1)) (uvalueMInt (extract v_10497 1 9)) (uvalueMInt (extract v_10497 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10507 0 1)) (uvalueMInt (extract v_10507 1 9)) (uvalueMInt (extract v_10507 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10515 0 1)) (uvalueMInt (extract v_10515 1 9)) (uvalueMInt (extract v_10515 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10525 0 1)) (uvalueMInt (extract v_10525 1 9)) (uvalueMInt (extract v_10525 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10533 0 1)) (uvalueMInt (extract v_10533 1 9)) (uvalueMInt (extract v_10533 9 32)))) 32))));
      pure ()
    pat_end
