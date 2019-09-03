def vcvtsi2sdl1 : instruction :=
  definst "vcvtsi2sdl" $ do
    pattern fun (v_3196 : reg (bv 32)) (v_3200 : reg (bv 128)) (v_3201 : reg (bv 128)) => do
      v_6916 <- getRegister v_3200;
      v_6918 <- getRegister v_3196;
      setRegister (lhs.of_reg v_3201) (concat (extract v_6916 0 64) (Float2MInt (Int2Float (svalueMInt v_6918) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3186 : Mem) (v_3189 : reg (bv 128)) (v_3190 : reg (bv 128)) => do
      v_12171 <- getRegister v_3189;
      v_12173 <- evaluateAddress v_3186;
      v_12174 <- load v_12173 4;
      setRegister (lhs.of_reg v_3190) (concat (extract v_12171 0 64) (Float2MInt (Int2Float (svalueMInt v_12174) 53 11) 64));
      pure ()
    pat_end
