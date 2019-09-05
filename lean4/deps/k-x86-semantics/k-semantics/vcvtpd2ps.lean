def vcvtpd2ps1 : instruction :=
  definst "vcvtpd2ps" $ do
    pattern fun (v_3120 : reg (bv 128)) (v_3121 : reg (bv 128)) => do
      v_5851 <- getRegister v_3120;
      setRegister (lhs.of_reg v_3121) (concat (expression.bv_nat 64 0) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5851 0 64) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_5851 64 128) 53 11) 24 8) 32)));
      pure ()
    pat_end;
    pattern fun (v_3124 : reg (bv 256)) (v_3126 : reg (bv 128)) => do
      v_5863 <- getRegister v_3124;
      setRegister (lhs.of_reg v_3126) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5863 0 64) 53 11) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5863 64 128) 53 11) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5863 128 192) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_5863 192 256) 53 11) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_3115 : Mem) (v_3116 : reg (bv 128)) => do
      v_9977 <- evaluateAddress v_3115;
      v_9978 <- load v_9977 16;
      setRegister (lhs.of_reg v_3116) (concat (expression.bv_nat 64 0) (concat (Float2MInt (roundFloat (MInt2Float (extract v_9978 0 64) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_9978 64 128) 53 11) 24 8) 32)));
      pure ()
    pat_end;
    pattern fun (v_3115 : Mem) (v_3116 : reg (bv 128)) => do
      v_9990 <- evaluateAddress v_3115;
      v_9991 <- load v_9990 16;
      setRegister (lhs.of_reg v_3116) (concat (Float2MInt (roundFloat (MInt2Float (extract v_9991 0 64) 53 11) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_9991 64 128) 53 11) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_9991 128 192) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_9991 192 256) 53 11) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_3115 : Mem) (v_3116 : reg (bv 128)) => do
      v_10012 <- evaluateAddress v_3115;
      v_10013 <- load v_10012 32;
      setRegister (lhs.of_reg v_3116) (concat (expression.bv_nat 64 0) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10013 0 64) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_10013 64 128) 53 11) 24 8) 32)));
      pure ()
    pat_end;
    pattern fun (v_3115 : Mem) (v_3116 : reg (bv 128)) => do
      v_10025 <- evaluateAddress v_3115;
      v_10026 <- load v_10025 32;
      setRegister (lhs.of_reg v_3116) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10026 0 64) 53 11) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10026 64 128) 53 11) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10026 128 192) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_10026 192 256) 53 11) 24 8) 32))));
      pure ()
    pat_end
