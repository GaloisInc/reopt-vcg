def cvtss2sd1 : instruction :=
  definst "cvtss2sd" $ do
    pattern fun (v_2601 : reg (bv 128)) (v_2602 : reg (bv 128)) => do
      v_4272 <- getRegister v_2602;
      v_4274 <- getRegister v_2601;
      v_4275 <- eval (extract v_4274 96 128);
      setRegister (lhs.of_reg v_2602) (concat (extract v_4272 0 64) (Float2MInt (roundFloat (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4275 0 1)) (uvalueMInt (extract v_4275 1 9)) (uvalueMInt (extract v_4275 9 32))) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_2595 : Mem) (v_2597 : reg (bv 128)) => do
      v_8483 <- getRegister v_2597;
      v_8485 <- evaluateAddress v_2595;
      v_8486 <- load v_8485 4;
      setRegister (lhs.of_reg v_2597) (concat (extract v_8483 0 64) (Float2MInt (roundFloat (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8486 0 1)) (uvalueMInt (extract v_8486 1 9)) (uvalueMInt (extract v_8486 9 32))) 53 11) 64));
      pure ()
    pat_end
