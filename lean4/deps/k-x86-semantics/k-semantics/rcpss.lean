def rcpss1 : instruction :=
  definst "rcpss" $ do
    pattern fun (v_2530 : reg (bv 128)) (v_2531 : reg (bv 128)) => do
      v_4236 <- getRegister v_2531;
      v_4238 <- getRegister v_2530;
      setRegister (lhs.of_reg v_2531) (concat (extract v_4236 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_4238 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2524 : Mem) (v_2527 : reg (bv 128)) => do
      v_10428 <- getRegister v_2527;
      v_10430 <- evaluateAddress v_2524;
      v_10431 <- load v_10430 4;
      setRegister (lhs.of_reg v_2527) (concat (extract v_10428 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float v_10431 24 8)) 32));
      pure ()
    pat_end
