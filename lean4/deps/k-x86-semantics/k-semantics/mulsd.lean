def mulsd1 : instruction :=
  definst "mulsd" $ do
    pattern fun (v_2765 : reg (bv 128)) (v_2766 : reg (bv 128)) => do
      v_4324 <- getRegister v_2766;
      v_4326 <- eval (extract v_4324 64 128);
      v_4334 <- getRegister v_2765;
      v_4335 <- eval (extract v_4334 64 128);
      setRegister (lhs.of_reg v_2766) (concat (extract v_4324 0 64) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4326 0 1)) (uvalueMInt (extract v_4326 1 12)) (uvalueMInt (extract v_4326 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4335 0 1)) (uvalueMInt (extract v_4335 1 12)) (uvalueMInt (extract v_4335 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2761 : Mem) (v_2762 : reg (bv 128)) => do
      v_9073 <- getRegister v_2762;
      v_9075 <- eval (extract v_9073 64 128);
      v_9083 <- evaluateAddress v_2761;
      v_9084 <- load v_9083 8;
      setRegister (lhs.of_reg v_2762) (concat (extract v_9073 0 64) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9075 0 1)) (uvalueMInt (extract v_9075 1 12)) (uvalueMInt (extract v_9075 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9084 0 1)) (uvalueMInt (extract v_9084 1 12)) (uvalueMInt (extract v_9084 12 64)))) 64));
      pure ()
    pat_end
