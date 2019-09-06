def vcvtps2pd1 : instruction :=
  definst "vcvtps2pd" $ do
    pattern fun (v_3197 : reg (bv 128)) (v_3198 : reg (bv 128)) => do
      v_6031 <- getRegister v_3197;
      setRegister (lhs.of_reg v_3198) (concat (Float2MInt (roundFloat (MInt2Float (extract v_6031 64 96) 24 8) 53 11) 64) (Float2MInt (roundFloat (MInt2Float (extract v_6031 96 128) 24 8) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3207 : reg (bv 128)) (v_3203 : reg (bv 256)) => do
      v_6046 <- getRegister v_3207;
      setRegister (lhs.of_reg v_3203) (concat (Float2MInt (roundFloat (MInt2Float (extract v_6046 0 32) 24 8) 53 11) 64) (concat (Float2MInt (roundFloat (MInt2Float (extract v_6046 32 64) 24 8) 53 11) 64) (concat (Float2MInt (roundFloat (MInt2Float (extract v_6046 64 96) 24 8) 53 11) 64) (Float2MInt (roundFloat (MInt2Float (extract v_6046 96 128) 24 8) 53 11) 64))));
      pure ()
    pat_end;
    pattern fun (v_3190 : Mem) (v_3193 : reg (bv 128)) => do
      v_10178 <- evaluateAddress v_3190;
      v_10179 <- load v_10178 8;
      setRegister (lhs.of_reg v_3193) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10179 0 32) 24 8) 53 11) 64) (Float2MInt (roundFloat (MInt2Float (extract v_10179 32 64) 24 8) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3199 : Mem) (v_3200 : reg (bv 256)) => do
      v_10190 <- evaluateAddress v_3199;
      v_10191 <- load v_10190 16;
      setRegister (lhs.of_reg v_3200) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10191 0 32) 24 8) 53 11) 64) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10191 32 64) 24 8) 53 11) 64) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10191 64 96) 24 8) 53 11) 64) (Float2MInt (roundFloat (MInt2Float (extract v_10191 96 128) 24 8) 53 11) 64))));
      pure ()
    pat_end
