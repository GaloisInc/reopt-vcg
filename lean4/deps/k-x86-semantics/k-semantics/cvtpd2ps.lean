def cvtpd2ps1 : instruction :=
  definst "cvtpd2ps" $ do
    pattern fun (v_2555 : reg (bv 128)) (v_2556 : reg (bv 128)) => do
      v_4133 <- getRegister v_2555;
      setRegister (lhs.of_reg v_2556) (concat (expression.bv_nat 64 0) (concat (Float2MInt (roundFloat (MInt2Float (extract v_4133 0 64) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_4133 64 128) 53 11) 24 8) 32)));
      pure ()
    pat_end;
    pattern fun (v_2550 : Mem) (v_2551 : reg (bv 128)) => do
      v_7840 <- evaluateAddress v_2550;
      v_7841 <- load v_7840 16;
      setRegister (lhs.of_reg v_2551) (concat (expression.bv_nat 64 0) (concat (Float2MInt (roundFloat (MInt2Float (extract v_7841 0 64) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_7841 64 128) 53 11) 24 8) 32)));
      pure ()
    pat_end
