def vcvtps2pd1 : instruction :=
  definst "vcvtps2pd" $ do
    pattern fun (v_3170 : reg (bv 128)) (v_3171 : reg (bv 128)) => do
      v_6004 <- getRegister v_3170;
      setRegister (lhs.of_reg v_3171) (concat (Float2MInt (roundFloat (MInt2Float (extract v_6004 64 96) 24 8) 53 11) 64) (Float2MInt (roundFloat (MInt2Float (extract v_6004 96 128) 24 8) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3180 : reg (bv 128)) (v_3178 : reg (bv 256)) => do
      v_6019 <- getRegister v_3180;
      setRegister (lhs.of_reg v_3178) (concat (Float2MInt (roundFloat (MInt2Float (extract v_6019 0 32) 24 8) 53 11) 64) (concat (Float2MInt (roundFloat (MInt2Float (extract v_6019 32 64) 24 8) 53 11) 64) (concat (Float2MInt (roundFloat (MInt2Float (extract v_6019 64 96) 24 8) 53 11) 64) (Float2MInt (roundFloat (MInt2Float (extract v_6019 96 128) 24 8) 53 11) 64))));
      pure ()
    pat_end;
    pattern fun (v_3165 : Mem) (v_3166 : reg (bv 128)) => do
      v_10151 <- evaluateAddress v_3165;
      v_10152 <- load v_10151 8;
      setRegister (lhs.of_reg v_3166) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10152 0 32) 24 8) 53 11) 64) (Float2MInt (roundFloat (MInt2Float (extract v_10152 32 64) 24 8) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3174 : Mem) (v_3175 : reg (bv 256)) => do
      v_10163 <- evaluateAddress v_3174;
      v_10164 <- load v_10163 16;
      setRegister (lhs.of_reg v_3175) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10164 0 32) 24 8) 53 11) 64) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10164 32 64) 24 8) 53 11) 64) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10164 64 96) 24 8) 53 11) 64) (Float2MInt (roundFloat (MInt2Float (extract v_10164 96 128) 24 8) 53 11) 64))));
      pure ()
    pat_end
