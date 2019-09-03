def mulss1 : instruction :=
  definst "mulss" $ do
    pattern fun (v_2774 : reg (bv 128)) (v_2775 : reg (bv 128)) => do
      v_4351 <- getRegister v_2775;
      v_4353 <- eval (extract v_4351 96 128);
      v_4361 <- getRegister v_2774;
      v_4362 <- eval (extract v_4361 96 128);
      setRegister (lhs.of_reg v_2775) (concat (extract v_4351 0 96) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4353 0 1)) (uvalueMInt (extract v_4353 1 9)) (uvalueMInt (extract v_4353 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4362 0 1)) (uvalueMInt (extract v_4362 1 9)) (uvalueMInt (extract v_4362 9 32)))) 32));
      pure ()
    pat_end;
    pattern fun (v_2770 : Mem) (v_2771 : reg (bv 128)) => do
      v_9096 <- getRegister v_2771;
      v_9098 <- eval (extract v_9096 96 128);
      v_9106 <- evaluateAddress v_2770;
      v_9107 <- load v_9106 4;
      setRegister (lhs.of_reg v_2771) (concat (extract v_9096 0 96) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9098 0 1)) (uvalueMInt (extract v_9098 1 9)) (uvalueMInt (extract v_9098 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9107 0 1)) (uvalueMInt (extract v_9107 1 9)) (uvalueMInt (extract v_9107 9 32)))) 32));
      pure ()
    pat_end
