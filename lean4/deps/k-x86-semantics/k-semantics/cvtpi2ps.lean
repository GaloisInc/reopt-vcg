def cvtpi2ps1 : instruction :=
  definst "cvtpi2ps" $ do
    pattern fun (v_2499 : Mem) (v_2500 : reg (bv 128)) => do
      v_8087 <- getRegister v_2500;
      v_8089 <- evaluateAddress v_2499;
      v_8090 <- load v_8089 8;
      setRegister (lhs.of_reg v_2500) (concat (extract v_8087 0 64) (concat (Float2MInt (Int2Float (svalueMInt (extract v_8090 0 32)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_8090 32 64)) 24 8) 32)));
      pure ()
    pat_end
