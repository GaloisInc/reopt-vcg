def cvtpd2ps1 : instruction :=
  definst "cvtpd2ps" $ do
    pattern fun (v_2490 : reg (bv 128)) (v_2491 : reg (bv 128)) => do
      v_4123 <- getRegister v_2490;
      setRegister (lhs.of_reg v_2491) (concat (expression.bv_nat 64 0) (concat (Float2MInt (roundFloat (MInt2Float (extract v_4123 0 64) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_4123 64 128) 53 11) 24 8) 32)));
      pure ()
    pat_end;
    pattern fun (v_2486 : Mem) (v_2487 : reg (bv 128)) => do
      v_8062 <- evaluateAddress v_2486;
      v_8063 <- load v_8062 16;
      setRegister (lhs.of_reg v_2487) (concat (expression.bv_nat 64 0) (concat (Float2MInt (roundFloat (MInt2Float (extract v_8063 0 64) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_8063 64 128) 53 11) 24 8) 32)));
      pure ()
    pat_end
