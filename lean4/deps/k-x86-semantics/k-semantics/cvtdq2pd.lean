def cvtdq2pd1 : instruction :=
  definst "cvtdq2pd" $ do
    pattern fun (v_2554 : reg (bv 128)) (v_2555 : reg (bv 128)) => do
      v_4102 <- getRegister v_2554;
      setRegister (lhs.of_reg v_2555) (concat (Float2MInt (Int2Float (svalueMInt (extract v_4102 64 96)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_4102 96 128)) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_2550 : Mem) (v_2551 : reg (bv 128)) => do
      v_7807 <- evaluateAddress v_2550;
      v_7808 <- load v_7807 8;
      setRegister (lhs.of_reg v_2551) (concat (Float2MInt (Int2Float (svalueMInt (extract v_7808 0 32)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_7808 32 64)) 53 11) 64));
      pure ()
    pat_end
