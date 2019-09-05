def rcpss1 : instruction :=
  definst "rcpss" $ do
    pattern fun (v_2504 : reg (bv 128)) (v_2505 : reg (bv 128)) => do
      v_4243 <- getRegister v_2505;
      v_4245 <- getRegister v_2504;
      setRegister (lhs.of_reg v_2505) (concat (extract v_4243 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_4245 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2499 : Mem) (v_2500 : reg (bv 128)) => do
      v_11172 <- getRegister v_2500;
      v_11174 <- evaluateAddress v_2499;
      v_11175 <- load v_11174 4;
      setRegister (lhs.of_reg v_2500) (concat (extract v_11172 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float v_11175 24 8)) 32));
      pure ()
    pat_end
