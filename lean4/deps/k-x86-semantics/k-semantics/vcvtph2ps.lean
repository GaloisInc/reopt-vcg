def vcvtph2ps1 : instruction :=
  definst "vcvtph2ps" $ do
    pattern fun (v_3134 : reg (bv 128)) (v_3135 : reg (bv 128)) => do
      v_5888 <- getRegister v_3134;
      setRegister (lhs.of_reg v_3135) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5888 64 80) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5888 80 96) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5888 96 112) 11 5) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_5888 112 128) 11 5) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_3144 : reg (bv 128)) (v_3142 : reg (bv 256)) => do
      v_5913 <- getRegister v_3144;
      setRegister (lhs.of_reg v_3142) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5913 0 16) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5913 16 32) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5913 32 48) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5913 48 64) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5913 64 80) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5913 80 96) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5913 96 112) 11 5) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_5913 112 128) 11 5) 24 8) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3129 : Mem) (v_3130 : reg (bv 128)) => do
      v_10047 <- evaluateAddress v_3129;
      v_10048 <- load v_10047 8;
      setRegister (lhs.of_reg v_3130) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10048 0 16) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10048 16 32) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10048 32 48) 11 5) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_10048 48 64) 11 5) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_3138 : Mem) (v_3139 : reg (bv 256)) => do
      v_10069 <- evaluateAddress v_3138;
      v_10070 <- load v_10069 16;
      setRegister (lhs.of_reg v_3139) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10070 0 16) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10070 16 32) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10070 32 48) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10070 48 64) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10070 64 80) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10070 80 96) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10070 96 112) 11 5) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_10070 112 128) 11 5) 24 8) 32))))))));
      pure ()
    pat_end
