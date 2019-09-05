def cvtsi2sdl1 : instruction :=
  definst "cvtsi2sdl" $ do
    pattern fun (v_2617 : reg (bv 32)) (v_2618 : reg (bv 128)) => do
      v_4218 <- getRegister v_2618;
      v_4220 <- getRegister v_2617;
      setRegister (lhs.of_reg v_2618) (concat (extract v_4218 0 64) (Float2MInt (Int2Float (svalueMInt v_4220) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_2612 : Mem) (v_2613 : reg (bv 128)) => do
      v_7923 <- getRegister v_2613;
      v_7925 <- evaluateAddress v_2612;
      v_7926 <- load v_7925 4;
      setRegister (lhs.of_reg v_2613) (concat (extract v_7923 0 64) (Float2MInt (Int2Float (svalueMInt v_7926) 53 11) 64));
      pure ()
    pat_end
