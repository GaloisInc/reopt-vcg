def vcvtss2sd1 : instruction :=
  definst "vcvtss2sd" $ do
    pattern fun (v_3341 : reg (bv 128)) (v_3342 : reg (bv 128)) (v_3343 : reg (bv 128)) => do
      v_6243 <- getRegister v_3342;
      v_6245 <- getRegister v_3341;
      setRegister (lhs.of_reg v_3343) (concat (extract v_6243 0 64) (Float2MInt (roundFloat (MInt2Float (extract v_6245 96 128) 24 8) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3333 : Mem) (v_3336 : reg (bv 128)) (v_3337 : reg (bv 128)) => do
      v_10269 <- getRegister v_3336;
      v_10271 <- evaluateAddress v_3333;
      v_10272 <- load v_10271 4;
      setRegister (lhs.of_reg v_3337) (concat (extract v_10269 0 64) (Float2MInt (roundFloat (MInt2Float v_10272 24 8) 53 11) 64));
      pure ()
    pat_end
