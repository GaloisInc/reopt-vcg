def rcpss1 : instruction :=
  definst "rcpss" $ do
    pattern fun (v_2451 : reg (bv 128)) (v_2452 : reg (bv 128)) => do
      v_4254 <- getRegister v_2452;
      v_4256 <- getRegister v_2451;
      v_4257 <- eval (extract v_4256 96 128);
      setRegister (lhs.of_reg v_2452) (concat (extract v_4254 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4257 0 1)) (uvalueMInt (extract v_4257 1 9)) (uvalueMInt (extract v_4257 9 32)))) 32));
      pure ()
    pat_end;
    pattern fun (v_2446 : Mem) (v_2447 : reg (bv 128)) => do
      v_12757 <- getRegister v_2447;
      v_12759 <- evaluateAddress v_2446;
      v_12760 <- load v_12759 4;
      setRegister (lhs.of_reg v_2447) (concat (extract v_12757 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12760 0 1)) (uvalueMInt (extract v_12760 1 9)) (uvalueMInt (extract v_12760 9 32)))) 32));
      pure ()
    pat_end
