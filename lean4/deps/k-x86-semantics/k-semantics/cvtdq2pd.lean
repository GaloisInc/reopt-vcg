def cvtdq2pd1 : instruction :=
  definst "cvtdq2pd" $ do
    pattern fun (v_2528 : reg (bv 128)) (v_2529 : reg (bv 128)) => do
      v_4081 <- getRegister v_2528;
      setRegister (lhs.of_reg v_2529) (concat (Float2MInt (Int2Float (svalueMInt (extract v_4081 64 96)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_4081 96 128)) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_2523 : Mem) (v_2524 : reg (bv 128)) => do
      v_7797 <- evaluateAddress v_2523;
      v_7798 <- load v_7797 8;
      setRegister (lhs.of_reg v_2524) (concat (Float2MInt (Int2Float (svalueMInt (extract v_7798 0 32)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_7798 32 64)) 53 11) 64));
      pure ()
    pat_end
