def cvtpi2ps1 : instruction :=
  definst "cvtpi2ps" $ do
    pattern fun (v_2510 : Mem) (v_2512 : reg (bv 128)) => do
      v_8371 <- getRegister v_2512;
      v_8373 <- evaluateAddress v_2510;
      v_8374 <- load v_8373 8;
      setRegister (lhs.of_reg v_2512) (concat (extract v_8371 0 64) (concat (Float2MInt (Int2Float (svalueMInt (extract v_8374 0 32)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_8374 32 64)) 24 8) 32)));
      pure ()
    pat_end
