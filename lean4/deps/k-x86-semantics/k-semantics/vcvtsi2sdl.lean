def vcvtsi2sdl1 : instruction :=
  definst "vcvtsi2sdl" $ do
    pattern fun (v_3184 : reg (bv 32)) (v_3187 : reg (bv 128)) (v_3188 : reg (bv 128)) => do
      v_6235 <- getRegister v_3187;
      v_6237 <- getRegister v_3184;
      setRegister (lhs.of_reg v_3188) (concat (extract v_6235 0 64) (Float2MInt (Int2Float (svalueMInt v_6237) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3173 : Mem) (v_3176 : reg (bv 128)) (v_3177 : reg (bv 128)) => do
      v_10443 <- getRegister v_3176;
      v_10445 <- evaluateAddress v_3173;
      v_10446 <- load v_10445 4;
      setRegister (lhs.of_reg v_3177) (concat (extract v_10443 0 64) (Float2MInt (Int2Float (svalueMInt v_10446) 53 11) 64));
      pure ()
    pat_end
