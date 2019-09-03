def vaddsd1 : instruction :=
  definst "vaddsd" $ do
    pattern fun (v_2627 : reg (bv 128)) (v_2628 : reg (bv 128)) (v_2629 : reg (bv 128)) => do
      v_5194 <- getRegister v_2628;
      v_5196 <- eval (extract v_5194 64 128);
      v_5204 <- getRegister v_2627;
      v_5205 <- eval (extract v_5204 64 128);
      setRegister (lhs.of_reg v_2629) (concat (extract v_5194 0 64) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5196 0 1)) (uvalueMInt (extract v_5196 1 12)) (uvalueMInt (extract v_5196 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5205 0 1)) (uvalueMInt (extract v_5205 1 12)) (uvalueMInt (extract v_5205 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2619 : Mem) (v_2622 : reg (bv 128)) (v_2623 : reg (bv 128)) => do
      v_10730 <- getRegister v_2622;
      v_10732 <- eval (extract v_10730 64 128);
      v_10740 <- evaluateAddress v_2619;
      v_10741 <- load v_10740 8;
      setRegister (lhs.of_reg v_2623) (concat (extract v_10730 0 64) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10732 0 1)) (uvalueMInt (extract v_10732 1 12)) (uvalueMInt (extract v_10732 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10741 0 1)) (uvalueMInt (extract v_10741 1 12)) (uvalueMInt (extract v_10741 12 64)))) 64));
      pure ()
    pat_end
