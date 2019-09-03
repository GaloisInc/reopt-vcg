def cvtps2pd1 : instruction :=
  definst "cvtps2pd" $ do
    pattern fun (v_2516 : reg (bv 128)) (v_2517 : reg (bv 128)) => do
      v_4164 <- getRegister v_2516;
      setRegister (lhs.of_reg v_2517) (concat (Float2MInt (roundFloat (MInt2Float (extract v_4164 64 96) 24 8) 53 11) 64) (Float2MInt (roundFloat (MInt2Float (extract v_4164 96 128) 24 8) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_2512 : Mem) (v_2513 : reg (bv 128)) => do
      v_8116 <- evaluateAddress v_2512;
      v_8117 <- load v_8116 8;
      setRegister (lhs.of_reg v_2513) (concat (Float2MInt (roundFloat (MInt2Float (extract v_8117 0 32) 24 8) 53 11) 64) (Float2MInt (roundFloat (MInt2Float (extract v_8117 32 64) 24 8) 53 11) 64));
      pure ()
    pat_end
