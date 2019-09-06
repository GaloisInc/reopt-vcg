def vcvtsi2sdl1 : instruction :=
  definst "vcvtsi2sdl" $ do
    pattern fun (v_3277 : reg (bv 32)) (v_3278 : reg (bv 128)) (v_3279 : reg (bv 128)) => do
      v_6184 <- getRegister v_3278;
      v_6186 <- getRegister v_3277;
      setRegister (lhs.of_reg v_3279) (concat (extract v_6184 0 64) (Float2MInt (Int2Float (svalueMInt v_6186) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3264 : Mem) (v_3267 : reg (bv 128)) (v_3268 : reg (bv 128)) => do
      v_10232 <- getRegister v_3267;
      v_10234 <- evaluateAddress v_3264;
      v_10235 <- load v_10234 4;
      setRegister (lhs.of_reg v_3268) (concat (extract v_10232 0 64) (Float2MInt (Int2Float (svalueMInt v_10235) 53 11) 64));
      pure ()
    pat_end
