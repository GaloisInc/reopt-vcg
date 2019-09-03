def cvtpi2pd1 : instruction :=
  definst "cvtpi2pd" $ do
    pattern fun (v_2506 : Mem) (v_2508 : reg (bv 128)) => do
      v_8359 <- evaluateAddress v_2506;
      v_8360 <- load v_8359 8;
      setRegister (lhs.of_reg v_2508) (concat (Float2MInt (Int2Float (svalueMInt (extract v_8360 0 32)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_8360 32 64)) 53 11) 64));
      pure ()
    pat_end
