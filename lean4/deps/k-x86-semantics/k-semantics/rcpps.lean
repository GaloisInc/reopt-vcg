def rcpps1 : instruction :=
  definst "rcpps" $ do
    pattern fun (v_2442 : reg (bv 128)) (v_2443 : reg (bv 128)) => do
      v_4205 <- getRegister v_2442;
      v_4206 <- eval (extract v_4205 0 32);
      v_4216 <- eval (extract v_4205 32 64);
      v_4226 <- eval (extract v_4205 64 96);
      v_4236 <- eval (extract v_4205 96 128);
      setRegister (lhs.of_reg v_2443) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4206 0 1)) (uvalueMInt (extract v_4206 1 9)) (uvalueMInt (extract v_4206 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4216 0 1)) (uvalueMInt (extract v_4216 1 9)) (uvalueMInt (extract v_4216 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4226 0 1)) (uvalueMInt (extract v_4226 1 9)) (uvalueMInt (extract v_4226 9 32)))) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4236 0 1)) (uvalueMInt (extract v_4236 1 9)) (uvalueMInt (extract v_4236 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_2437 : Mem) (v_2438 : reg (bv 128)) => do
      v_12711 <- evaluateAddress v_2437;
      v_12712 <- load v_12711 16;
      v_12713 <- eval (extract v_12712 0 32);
      v_12723 <- eval (extract v_12712 32 64);
      v_12733 <- eval (extract v_12712 64 96);
      v_12743 <- eval (extract v_12712 96 128);
      setRegister (lhs.of_reg v_2438) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12713 0 1)) (uvalueMInt (extract v_12713 1 9)) (uvalueMInt (extract v_12713 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12723 0 1)) (uvalueMInt (extract v_12723 1 9)) (uvalueMInt (extract v_12723 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12733 0 1)) (uvalueMInt (extract v_12733 1 9)) (uvalueMInt (extract v_12733 9 32)))) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12743 0 1)) (uvalueMInt (extract v_12743 1 9)) (uvalueMInt (extract v_12743 9 32)))) 32))));
      pure ()
    pat_end
