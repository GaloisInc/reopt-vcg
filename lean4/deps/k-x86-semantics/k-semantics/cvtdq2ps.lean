def cvtdq2ps1 : instruction :=
  definst "cvtdq2ps" $ do
    pattern fun (v_2472 : reg (bv 128)) (v_2473 : reg (bv 128)) => do
      v_4086 <- getRegister v_2472;
      setRegister (lhs.of_reg v_2473) (concat (Float2MInt (Int2Float (svalueMInt (extract v_4086 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_4086 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_4086 64 96)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_4086 96 128)) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_2468 : Mem) (v_2469 : reg (bv 128)) => do
      v_8031 <- evaluateAddress v_2468;
      v_8032 <- load v_8031 16;
      setRegister (lhs.of_reg v_2469) (concat (Float2MInt (Int2Float (svalueMInt (extract v_8032 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_8032 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_8032 64 96)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_8032 96 128)) 24 8) 32))));
      pure ()
    pat_end
