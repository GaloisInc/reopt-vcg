def vcvtsi2sdl1 : instruction :=
  definst "vcvtsi2sdl" $ do
    pattern fun (v_3252 : reg (bv 32)) (v_3250 : reg (bv 128)) (v_3251 : reg (bv 128)) => do
      v_6157 <- getRegister v_3250;
      v_6159 <- getRegister v_3252;
      setRegister (lhs.of_reg v_3251) (concat (extract v_6157 0 64) (Float2MInt (Int2Float (svalueMInt v_6159) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3239 : Mem) (v_3240 : reg (bv 128)) (v_3241 : reg (bv 128)) => do
      v_10205 <- getRegister v_3240;
      v_10207 <- evaluateAddress v_3239;
      v_10208 <- load v_10207 4;
      setRegister (lhs.of_reg v_3241) (concat (extract v_10205 0 64) (Float2MInt (Int2Float (svalueMInt v_10208) 53 11) 64));
      pure ()
    pat_end
