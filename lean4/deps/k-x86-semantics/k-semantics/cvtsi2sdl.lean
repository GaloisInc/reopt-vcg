def cvtsi2sdl1 : instruction :=
  definst "cvtsi2sdl" $ do
    pattern fun (v_2564 : reg (bv 32)) (v_2566 : reg (bv 128)) => do
      v_4224 <- getRegister v_2566;
      v_4226 <- getRegister v_2564;
      setRegister (lhs.of_reg v_2566) (concat (extract v_4224 0 64) (Float2MInt (Int2Float (svalueMInt v_4226) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_2559 : Mem) (v_2561 : reg (bv 128)) => do
      v_8447 <- getRegister v_2561;
      v_8449 <- evaluateAddress v_2559;
      v_8450 <- load v_8449 4;
      setRegister (lhs.of_reg v_2561) (concat (extract v_8447 0 64) (Float2MInt (Int2Float (svalueMInt v_8450) 53 11) 64));
      pure ()
    pat_end
