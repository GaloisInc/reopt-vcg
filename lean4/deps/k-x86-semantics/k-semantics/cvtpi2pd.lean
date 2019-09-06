def cvtpi2pd1 : instruction :=
  definst "cvtpi2pd" $ do
    pattern fun (v_2586 : Mem) (v_2587 : reg (bv 128)) => do
      v_7863 <- evaluateAddress v_2586;
      v_7864 <- load v_7863 8;
      setRegister (lhs.of_reg v_2587) (concat (Float2MInt (Int2Float (svalueMInt (extract v_7864 0 32)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_7864 32 64)) 53 11) 64));
      pure ()
    pat_end
