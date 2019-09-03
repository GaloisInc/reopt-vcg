def cvtdq2ps1 : instruction :=
  definst "cvtdq2ps" $ do
    pattern fun (v_2485 : reg (bv 128)) (v_2486 : reg (bv 128)) => do
      v_4072 <- getRegister v_2485;
      setRegister (lhs.of_reg v_2486) (concat (Float2MInt (Int2Float (svalueMInt (extract v_4072 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_4072 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_4072 64 96)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_4072 96 128)) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_2479 : Mem) (v_2481 : reg (bv 128)) => do
      v_8303 <- evaluateAddress v_2479;
      v_8304 <- load v_8303 16;
      setRegister (lhs.of_reg v_2481) (concat (Float2MInt (Int2Float (svalueMInt (extract v_8304 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_8304 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_8304 64 96)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_8304 96 128)) 24 8) 32))));
      pure ()
    pat_end
