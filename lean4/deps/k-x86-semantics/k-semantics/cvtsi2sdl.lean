def cvtsi2sdl1 : instruction :=
  definst "cvtsi2sdl" $ do
    pattern fun (v_2553 : reg (bv 32)) (v_2552 : reg (bv 128)) => do
      v_4208 <- getRegister v_2552;
      v_4210 <- getRegister v_2553;
      setRegister (lhs.of_reg v_2552) (concat (extract v_4208 0 64) (Float2MInt (Int2Float (svalueMInt v_4210) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_2548 : Mem) (v_2549 : reg (bv 128)) => do
      v_8145 <- getRegister v_2549;
      v_8147 <- evaluateAddress v_2548;
      v_8148 <- load v_8147 4;
      setRegister (lhs.of_reg v_2549) (concat (extract v_8145 0 64) (Float2MInt (Int2Float (svalueMInt v_8148) 53 11) 64));
      pure ()
    pat_end
