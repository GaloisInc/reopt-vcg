def vcvtph2ps1 : instruction :=
  definst "vcvtph2ps" $ do
    pattern fun (v_3070 : reg (bv 128)) (v_3071 : reg (bv 128)) => do
      v_5966 <- getRegister v_3070;
      setRegister (lhs.of_reg v_3071) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5966 64 80) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5966 80 96) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5966 96 112) 11 5) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_5966 112 128) 11 5) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_3080 : reg (bv 128)) (v_3077 : reg (bv 256)) => do
      v_5991 <- getRegister v_3080;
      setRegister (lhs.of_reg v_3077) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5991 0 16) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5991 16 32) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5991 32 48) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5991 48 64) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5991 64 80) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5991 80 96) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5991 96 112) 11 5) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_5991 112 128) 11 5) 24 8) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3063 : Mem) (v_3066 : reg (bv 128)) => do
      v_10285 <- evaluateAddress v_3063;
      v_10286 <- load v_10285 8;
      setRegister (lhs.of_reg v_3066) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10286 0 16) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10286 16 32) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10286 32 48) 11 5) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_10286 48 64) 11 5) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_3072 : Mem) (v_3073 : reg (bv 256)) => do
      v_10307 <- evaluateAddress v_3072;
      v_10308 <- load v_10307 16;
      setRegister (lhs.of_reg v_3073) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10308 0 16) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10308 16 32) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10308 32 48) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10308 48 64) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10308 64 80) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10308 80 96) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10308 96 112) 11 5) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_10308 112 128) 11 5) 24 8) 32))))))));
      pure ()
    pat_end
