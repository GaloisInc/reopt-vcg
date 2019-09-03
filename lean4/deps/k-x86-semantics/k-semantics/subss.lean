def subss1 : instruction :=
  definst "subss" $ do
    pattern fun (v_3245 : reg (bv 128)) (v_3246 : reg (bv 128)) => do
      v_7470 <- getRegister v_3246;
      v_7472 <- eval (extract v_7470 96 128);
      v_7480 <- getRegister v_3245;
      v_7481 <- eval (extract v_7480 96 128);
      setRegister (lhs.of_reg v_3246) (concat (extract v_7470 0 96) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7472 0 1)) (uvalueMInt (extract v_7472 1 9)) (uvalueMInt (extract v_7472 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7481 0 1)) (uvalueMInt (extract v_7481 1 9)) (uvalueMInt (extract v_7481 9 32)))) 32));
      pure ()
    pat_end;
    pattern fun (v_3240 : Mem) (v_3241 : reg (bv 128)) => do
      v_10611 <- getRegister v_3241;
      v_10613 <- eval (extract v_10611 96 128);
      v_10621 <- evaluateAddress v_3240;
      v_10622 <- load v_10621 4;
      setRegister (lhs.of_reg v_3241) (concat (extract v_10611 0 96) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10613 0 1)) (uvalueMInt (extract v_10613 1 9)) (uvalueMInt (extract v_10613 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10622 0 1)) (uvalueMInt (extract v_10622 1 9)) (uvalueMInt (extract v_10622 9 32)))) 32));
      pure ()
    pat_end
