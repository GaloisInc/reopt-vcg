def vcvtpd2ps1 : instruction :=
  definst "vcvtpd2ps" $ do
    pattern fun (v_3056 : reg (bv 128)) (v_3057 : reg (bv 128)) => do
      v_5929 <- getRegister v_3056;
      setRegister (lhs.of_reg v_3057) (concat (expression.bv_nat 64 0) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5929 0 64) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_5929 64 128) 53 11) 24 8) 32)));
      pure ()
    pat_end;
    pattern fun (v_3059 : reg (bv 256)) (v_3062 : reg (bv 128)) => do
      v_5941 <- getRegister v_3059;
      setRegister (lhs.of_reg v_3062) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5941 0 64) 53 11) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5941 64 128) 53 11) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5941 128 192) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_5941 192 256) 53 11) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_3049 : Mem) (v_3052 : reg (bv 128)) => do
      v_10215 <- evaluateAddress v_3049;
      v_10216 <- load v_10215 16;
      setRegister (lhs.of_reg v_3052) (concat (expression.bv_nat 64 0) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10216 0 64) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_10216 64 128) 53 11) 24 8) 32)));
      pure ()
    pat_end;
    pattern fun (v_3049 : Mem) (v_3052 : reg (bv 128)) => do
      v_10228 <- evaluateAddress v_3049;
      v_10229 <- load v_10228 16;
      setRegister (lhs.of_reg v_3052) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10229 0 64) 53 11) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10229 64 128) 53 11) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10229 128 192) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_10229 192 256) 53 11) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_3049 : Mem) (v_3052 : reg (bv 128)) => do
      v_10250 <- evaluateAddress v_3049;
      v_10251 <- load v_10250 32;
      setRegister (lhs.of_reg v_3052) (concat (expression.bv_nat 64 0) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10251 0 64) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_10251 64 128) 53 11) 24 8) 32)));
      pure ()
    pat_end;
    pattern fun (v_3049 : Mem) (v_3052 : reg (bv 128)) => do
      v_10263 <- evaluateAddress v_3049;
      v_10264 <- load v_10263 32;
      setRegister (lhs.of_reg v_3052) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10264 0 64) 53 11) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10264 64 128) 53 11) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10264 128 192) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_10264 192 256) 53 11) 24 8) 32))));
      pure ()
    pat_end
