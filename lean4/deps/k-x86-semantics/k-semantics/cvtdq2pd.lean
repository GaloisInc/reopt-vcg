def cvtdq2pd1 : instruction :=
  definst "cvtdq2pd" $ do
    pattern fun (v_2463 : reg (bv 128)) (v_2464 : reg (bv 128)) => do
      v_4071 <- getRegister v_2463;
      setRegister (lhs.of_reg v_2464) (concat (Float2MInt (Int2Float (svalueMInt (extract v_4071 64 96)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_4071 96 128)) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_2459 : Mem) (v_2460 : reg (bv 128)) => do
      v_8019 <- evaluateAddress v_2459;
      v_8020 <- load v_8019 8;
      setRegister (lhs.of_reg v_2460) (concat (Float2MInt (Int2Float (svalueMInt (extract v_8020 0 32)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_8020 32 64)) 53 11) 64));
      pure ()
    pat_end
