def vcvtpd2ps1 : instruction :=
  definst "vcvtpd2ps" $ do
    pattern fun (v_3147 : reg (bv 128)) (v_3148 : reg (bv 128)) => do
      v_5878 <- getRegister v_3147;
      setRegister (lhs.of_reg v_3148) (concat (expression.bv_nat 64 0) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5878 0 64) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_5878 64 128) 53 11) 24 8) 32)));
      pure ()
    pat_end;
    pattern fun (v_3149 : reg (bv 256)) (v_3153 : reg (bv 128)) => do
      v_5890 <- getRegister v_3149;
      setRegister (lhs.of_reg v_3153) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5890 0 64) 53 11) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5890 64 128) 53 11) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5890 128 192) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_5890 192 256) 53 11) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_3140 : Mem) (v_3143 : reg (bv 128)) => do
      v_10004 <- evaluateAddress v_3140;
      v_10005 <- load v_10004 16;
      setRegister (lhs.of_reg v_3143) (concat (expression.bv_nat 64 0) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10005 0 64) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_10005 64 128) 53 11) 24 8) 32)));
      pure ()
    pat_end;
    pattern fun (v_3140 : Mem) (v_3143 : reg (bv 128)) => do
      v_10017 <- evaluateAddress v_3140;
      v_10018 <- load v_10017 16;
      setRegister (lhs.of_reg v_3143) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10018 0 64) 53 11) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10018 64 128) 53 11) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10018 128 192) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_10018 192 256) 53 11) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_3140 : Mem) (v_3143 : reg (bv 128)) => do
      v_10039 <- evaluateAddress v_3140;
      v_10040 <- load v_10039 32;
      setRegister (lhs.of_reg v_3143) (concat (expression.bv_nat 64 0) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10040 0 64) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_10040 64 128) 53 11) 24 8) 32)));
      pure ()
    pat_end;
    pattern fun (v_3140 : Mem) (v_3143 : reg (bv 128)) => do
      v_10052 <- evaluateAddress v_3140;
      v_10053 <- load v_10052 32;
      setRegister (lhs.of_reg v_3143) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10053 0 64) 53 11) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10053 64 128) 53 11) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10053 128 192) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_10053 192 256) 53 11) 24 8) 32))));
      pure ()
    pat_end
