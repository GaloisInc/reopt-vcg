def cvtdq2ps1 : instruction :=
  definst "cvtdq2ps" $ do
    pattern fun (v_2563 : reg (bv 128)) (v_2564 : reg (bv 128)) => do
      v_4117 <- getRegister v_2563;
      setRegister (lhs.of_reg v_2564) (concat (Float2MInt (Int2Float (svalueMInt (extract v_4117 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_4117 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_4117 64 96)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_4117 96 128)) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_2559 : Mem) (v_2560 : reg (bv 128)) => do
      v_7819 <- evaluateAddress v_2559;
      v_7820 <- load v_7819 16;
      setRegister (lhs.of_reg v_2560) (concat (Float2MInt (Int2Float (svalueMInt (extract v_7820 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_7820 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_7820 64 96)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_7820 96 128)) 24 8) 32))));
      pure ()
    pat_end
