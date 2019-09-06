def cvtsi2sdl1 : instruction :=
  definst "cvtsi2sdl" $ do
    pattern fun (v_2643 : reg (bv 32)) (v_2644 : reg (bv 128)) => do
      v_4239 <- getRegister v_2644;
      v_4241 <- getRegister v_2643;
      setRegister (lhs.of_reg v_2644) (concat (extract v_4239 0 64) (Float2MInt (Int2Float (svalueMInt v_4241) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_2639 : Mem) (v_2640 : reg (bv 128)) => do
      v_7933 <- getRegister v_2640;
      v_7935 <- evaluateAddress v_2639;
      v_7936 <- load v_7935 4;
      setRegister (lhs.of_reg v_2640) (concat (extract v_7933 0 64) (Float2MInt (Int2Float (svalueMInt v_7936) 53 11) 64));
      pure ()
    pat_end
