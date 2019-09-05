def cvtdq2ps1 : instruction :=
  definst "cvtdq2ps" $ do
    pattern fun (v_2537 : reg (bv 128)) (v_2538 : reg (bv 128)) => do
      v_4096 <- getRegister v_2537;
      setRegister (lhs.of_reg v_2538) (concat (Float2MInt (Int2Float (svalueMInt (extract v_4096 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_4096 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_4096 64 96)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_4096 96 128)) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_2532 : Mem) (v_2533 : reg (bv 128)) => do
      v_7809 <- evaluateAddress v_2532;
      v_7810 <- load v_7809 16;
      setRegister (lhs.of_reg v_2533) (concat (Float2MInt (Int2Float (svalueMInt (extract v_7810 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_7810 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_7810 64 96)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_7810 96 128)) 24 8) 32))));
      pure ()
    pat_end
