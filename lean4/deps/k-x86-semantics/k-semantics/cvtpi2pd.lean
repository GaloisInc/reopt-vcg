def cvtpi2pd1 : instruction :=
  definst "cvtpi2pd" $ do
    pattern fun (v_2559 : Mem) (v_2560 : reg (bv 128)) => do
      v_7853 <- evaluateAddress v_2559;
      v_7854 <- load v_7853 8;
      setRegister (lhs.of_reg v_2560) (concat (Float2MInt (Int2Float (svalueMInt (extract v_7854 0 32)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_7854 32 64)) 53 11) 64));
      pure ()
    pat_end
