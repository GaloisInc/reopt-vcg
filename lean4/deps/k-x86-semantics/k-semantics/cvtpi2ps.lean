def cvtpi2ps1 : instruction :=
  definst "cvtpi2ps" $ do
    pattern fun (v_2563 : Mem) (v_2564 : reg (bv 128)) => do
      v_7865 <- getRegister v_2564;
      v_7867 <- evaluateAddress v_2563;
      v_7868 <- load v_7867 8;
      setRegister (lhs.of_reg v_2564) (concat (extract v_7865 0 64) (concat (Float2MInt (Int2Float (svalueMInt (extract v_7868 0 32)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_7868 32 64)) 24 8) 32)));
      pure ()
    pat_end
