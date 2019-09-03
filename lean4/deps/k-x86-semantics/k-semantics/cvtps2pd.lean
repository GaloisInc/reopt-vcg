def cvtps2pd1 : instruction :=
  definst "cvtps2pd" $ do
    pattern fun (v_2529 : reg (bv 128)) (v_2530 : reg (bv 128)) => do
      v_4162 <- getRegister v_2529;
      v_4163 <- eval (extract v_4162 64 96);
      v_4173 <- eval (extract v_4162 96 128);
      setRegister (lhs.of_reg v_2530) (concat (Float2MInt (roundFloat (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4163 0 1)) (uvalueMInt (extract v_4163 1 9)) (uvalueMInt (extract v_4163 9 32))) 53 11) 64) (Float2MInt (roundFloat (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4173 0 1)) (uvalueMInt (extract v_4173 1 9)) (uvalueMInt (extract v_4173 9 32))) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_2523 : Mem) (v_2525 : reg (bv 128)) => do
      v_8400 <- evaluateAddress v_2523;
      v_8401 <- load v_8400 8;
      v_8402 <- eval (extract v_8401 0 32);
      v_8412 <- eval (extract v_8401 32 64);
      setRegister (lhs.of_reg v_2525) (concat (Float2MInt (roundFloat (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8402 0 1)) (uvalueMInt (extract v_8402 1 9)) (uvalueMInt (extract v_8402 9 32))) 53 11) 64) (Float2MInt (roundFloat (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8412 0 1)) (uvalueMInt (extract v_8412 1 9)) (uvalueMInt (extract v_8412 9 32))) 53 11) 64));
      pure ()
    pat_end
