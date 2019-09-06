def vcvtph2ps1 : instruction :=
  definst "vcvtph2ps" $ do
    pattern fun (v_3161 : reg (bv 128)) (v_3162 : reg (bv 128)) => do
      v_5915 <- getRegister v_3161;
      setRegister (lhs.of_reg v_3162) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5915 64 80) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5915 80 96) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5915 96 112) 11 5) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_5915 112 128) 11 5) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_3171 : reg (bv 128)) (v_3167 : reg (bv 256)) => do
      v_5940 <- getRegister v_3171;
      setRegister (lhs.of_reg v_3167) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5940 0 16) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5940 16 32) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5940 32 48) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5940 48 64) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5940 64 80) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5940 80 96) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_5940 96 112) 11 5) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_5940 112 128) 11 5) 24 8) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3154 : Mem) (v_3157 : reg (bv 128)) => do
      v_10074 <- evaluateAddress v_3154;
      v_10075 <- load v_10074 8;
      setRegister (lhs.of_reg v_3157) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10075 0 16) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10075 16 32) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10075 32 48) 11 5) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_10075 48 64) 11 5) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_3163 : Mem) (v_3164 : reg (bv 256)) => do
      v_10096 <- evaluateAddress v_3163;
      v_10097 <- load v_10096 16;
      setRegister (lhs.of_reg v_3164) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10097 0 16) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10097 16 32) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10097 32 48) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10097 48 64) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10097 64 80) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10097 80 96) 11 5) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10097 96 112) 11 5) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_10097 112 128) 11 5) 24 8) 32))))))));
      pure ()
    pat_end
