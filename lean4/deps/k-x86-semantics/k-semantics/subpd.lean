def subpd1 : instruction :=
  definst "subpd" $ do
    pattern fun (v_3192 : reg (bv 128)) (v_3193 : reg (bv 128)) => do
      v_7187 <- getRegister v_3193;
      v_7188 <- eval (extract v_7187 0 64);
      v_7196 <- getRegister v_3192;
      v_7197 <- eval (extract v_7196 0 64);
      v_7207 <- eval (extract v_7187 64 128);
      v_7215 <- eval (extract v_7196 64 128);
      setRegister (lhs.of_reg v_3193) (concat (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7188 0 1)) (uvalueMInt (extract v_7188 1 12)) (uvalueMInt (extract v_7188 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7197 0 1)) (uvalueMInt (extract v_7197 1 12)) (uvalueMInt (extract v_7197 12 64)))) 64) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7207 0 1)) (uvalueMInt (extract v_7207 1 12)) (uvalueMInt (extract v_7207 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7215 0 1)) (uvalueMInt (extract v_7215 1 12)) (uvalueMInt (extract v_7215 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_3187 : Mem) (v_3188 : reg (bv 128)) => do
      v_10427 <- getRegister v_3188;
      v_10428 <- eval (extract v_10427 0 64);
      v_10436 <- evaluateAddress v_3187;
      v_10437 <- load v_10436 16;
      v_10438 <- eval (extract v_10437 0 64);
      v_10448 <- eval (extract v_10427 64 128);
      v_10456 <- eval (extract v_10437 64 128);
      setRegister (lhs.of_reg v_3188) (concat (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10428 0 1)) (uvalueMInt (extract v_10428 1 12)) (uvalueMInt (extract v_10428 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10438 0 1)) (uvalueMInt (extract v_10438 1 12)) (uvalueMInt (extract v_10438 12 64)))) 64) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10448 0 1)) (uvalueMInt (extract v_10448 1 12)) (uvalueMInt (extract v_10448 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10456 0 1)) (uvalueMInt (extract v_10456 1 12)) (uvalueMInt (extract v_10456 12 64)))) 64));
      pure ()
    pat_end
