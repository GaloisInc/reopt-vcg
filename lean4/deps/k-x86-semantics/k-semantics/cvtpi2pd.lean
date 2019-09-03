def cvtpi2pd1 : instruction :=
  definst "cvtpi2pd" $ do
    pattern fun (v_2495 : Mem) (v_2496 : reg (bv 128)) => do
      v_8075 <- evaluateAddress v_2495;
      v_8076 <- load v_8075 8;
      setRegister (lhs.of_reg v_2496) (concat (Float2MInt (Int2Float (svalueMInt (extract v_8076 0 32)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_8076 32 64)) 53 11) 64));
      pure ()
    pat_end
