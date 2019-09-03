def rcpss1 : instruction :=
  definst "rcpss" $ do
    pattern fun (v_2439 : reg (bv 128)) (v_2440 : reg (bv 128)) => do
      v_4215 <- getRegister v_2440;
      v_4217 <- getRegister v_2439;
      setRegister (lhs.of_reg v_2440) (concat (extract v_4215 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_4217 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2433 : Mem) (v_2436 : reg (bv 128)) => do
      v_12837 <- getRegister v_2436;
      v_12839 <- evaluateAddress v_2433;
      v_12840 <- load v_12839 4;
      setRegister (lhs.of_reg v_2436) (concat (extract v_12837 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float v_12840 24 8)) 32));
      pure ()
    pat_end
