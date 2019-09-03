def vcvtsi2ssl1 : instruction :=
  definst "vcvtsi2ssl" $ do
    pattern fun (v_3221 : reg (bv 32)) (v_3224 : reg (bv 128)) (v_3225 : reg (bv 128)) => do
      v_6267 <- getRegister v_3224;
      v_6269 <- getRegister v_3221;
      setRegister (lhs.of_reg v_3225) (concat (extract v_6267 0 96) (Float2MInt (Int2Float (svalueMInt v_6269) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (v_3210 : Mem) (v_3213 : reg (bv 128)) (v_3214 : reg (bv 128)) => do
      v_10462 <- getRegister v_3213;
      v_10464 <- evaluateAddress v_3210;
      v_10465 <- load v_10464 4;
      setRegister (lhs.of_reg v_3214) (concat (extract v_10462 0 96) (Float2MInt (Int2Float (svalueMInt v_10465) 24 8) 32));
      pure ()
    pat_end
