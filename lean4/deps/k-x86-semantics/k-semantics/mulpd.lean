def mulpd1 : instruction :=
  definst "mulpd" $ do
    pattern fun (v_2740 : reg (bv 128)) (v_2741 : reg (bv 128)) => do
      v_4177 <- getRegister v_2741;
      v_4178 <- eval (extract v_4177 0 64);
      v_4186 <- getRegister v_2740;
      v_4187 <- eval (extract v_4186 0 64);
      v_4197 <- eval (extract v_4177 64 128);
      v_4205 <- eval (extract v_4186 64 128);
      setRegister (lhs.of_reg v_2741) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4178 0 1)) (uvalueMInt (extract v_4178 1 12)) (uvalueMInt (extract v_4178 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4187 0 1)) (uvalueMInt (extract v_4187 1 12)) (uvalueMInt (extract v_4187 12 64)))) 64) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4197 0 1)) (uvalueMInt (extract v_4197 1 12)) (uvalueMInt (extract v_4197 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4205 0 1)) (uvalueMInt (extract v_4205 1 12)) (uvalueMInt (extract v_4205 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2736 : Mem) (v_2737 : reg (bv 128)) => do
      v_8934 <- getRegister v_2737;
      v_8935 <- eval (extract v_8934 0 64);
      v_8943 <- evaluateAddress v_2736;
      v_8944 <- load v_8943 16;
      v_8945 <- eval (extract v_8944 0 64);
      v_8955 <- eval (extract v_8934 64 128);
      v_8963 <- eval (extract v_8944 64 128);
      setRegister (lhs.of_reg v_2737) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8935 0 1)) (uvalueMInt (extract v_8935 1 12)) (uvalueMInt (extract v_8935 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8945 0 1)) (uvalueMInt (extract v_8945 1 12)) (uvalueMInt (extract v_8945 12 64)))) 64) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8955 0 1)) (uvalueMInt (extract v_8955 1 12)) (uvalueMInt (extract v_8955 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8963 0 1)) (uvalueMInt (extract v_8963 1 12)) (uvalueMInt (extract v_8963 12 64)))) 64));
      pure ()
    pat_end
