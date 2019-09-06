def cvtpd2ps1 : instruction :=
  definst "cvtpd2ps" $ do
    pattern fun (v_2581 : reg (bv 128)) (v_2582 : reg (bv 128)) => do
      v_4154 <- getRegister v_2581;
      setRegister (lhs.of_reg v_2582) (concat (expression.bv_nat 64 0) (concat (Float2MInt (roundFloat (MInt2Float (extract v_4154 0 64) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_4154 64 128) 53 11) 24 8) 32)));
      pure ()
    pat_end;
    pattern fun (v_2577 : Mem) (v_2578 : reg (bv 128)) => do
      v_7850 <- evaluateAddress v_2577;
      v_7851 <- load v_7850 16;
      setRegister (lhs.of_reg v_2578) (concat (expression.bv_nat 64 0) (concat (Float2MInt (roundFloat (MInt2Float (extract v_7851 0 64) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_7851 64 128) 53 11) 24 8) 32)));
      pure ()
    pat_end
