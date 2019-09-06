def cvtpi2ps1 : instruction :=
  definst "cvtpi2ps" $ do
    pattern fun (v_2590 : Mem) (v_2591 : reg (bv 128)) => do
      v_7875 <- getRegister v_2591;
      v_7877 <- evaluateAddress v_2590;
      v_7878 <- load v_7877 8;
      setRegister (lhs.of_reg v_2591) (concat (extract v_7875 0 64) (concat (Float2MInt (Int2Float (svalueMInt (extract v_7878 0 32)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_7878 32 64)) 24 8) 32)));
      pure ()
    pat_end
