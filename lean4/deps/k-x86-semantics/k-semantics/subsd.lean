def subsd1 : instruction :=
  definst "subsd" $ do
    pattern fun (v_3236 : reg (bv 128)) (v_3237 : reg (bv 128)) => do
      v_7443 <- getRegister v_3237;
      v_7445 <- eval (extract v_7443 64 128);
      v_7453 <- getRegister v_3236;
      v_7454 <- eval (extract v_7453 64 128);
      setRegister (lhs.of_reg v_3237) (concat (extract v_7443 0 64) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7445 0 1)) (uvalueMInt (extract v_7445 1 12)) (uvalueMInt (extract v_7445 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7454 0 1)) (uvalueMInt (extract v_7454 1 12)) (uvalueMInt (extract v_7454 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_3231 : Mem) (v_3232 : reg (bv 128)) => do
      v_10588 <- getRegister v_3232;
      v_10590 <- eval (extract v_10588 64 128);
      v_10598 <- evaluateAddress v_3231;
      v_10599 <- load v_10598 8;
      setRegister (lhs.of_reg v_3232) (concat (extract v_10588 0 64) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10590 0 1)) (uvalueMInt (extract v_10590 1 12)) (uvalueMInt (extract v_10590 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10599 0 1)) (uvalueMInt (extract v_10599 1 12)) (uvalueMInt (extract v_10599 12 64)))) 64));
      pure ()
    pat_end
