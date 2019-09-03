def vcvtps2pd1 : instruction :=
  definst "vcvtps2pd" $ do
    pattern fun (v_3106 : reg (bv 128)) (v_3107 : reg (bv 128)) => do
      v_6082 <- getRegister v_3106;
      setRegister (lhs.of_reg v_3107) (concat (Float2MInt (roundFloat (MInt2Float (extract v_6082 64 96) 24 8) 53 11) 64) (Float2MInt (roundFloat (MInt2Float (extract v_6082 96 128) 24 8) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3116 : reg (bv 128)) (v_3113 : reg (bv 256)) => do
      v_6097 <- getRegister v_3116;
      setRegister (lhs.of_reg v_3113) (concat (Float2MInt (roundFloat (MInt2Float (extract v_6097 0 32) 24 8) 53 11) 64) (concat (Float2MInt (roundFloat (MInt2Float (extract v_6097 32 64) 24 8) 53 11) 64) (concat (Float2MInt (roundFloat (MInt2Float (extract v_6097 64 96) 24 8) 53 11) 64) (Float2MInt (roundFloat (MInt2Float (extract v_6097 96 128) 24 8) 53 11) 64))));
      pure ()
    pat_end;
    pattern fun (v_3099 : Mem) (v_3102 : reg (bv 128)) => do
      v_10389 <- evaluateAddress v_3099;
      v_10390 <- load v_10389 8;
      setRegister (lhs.of_reg v_3102) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10390 0 32) 24 8) 53 11) 64) (Float2MInt (roundFloat (MInt2Float (extract v_10390 32 64) 24 8) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3108 : Mem) (v_3109 : reg (bv 256)) => do
      v_10401 <- evaluateAddress v_3108;
      v_10402 <- load v_10401 16;
      setRegister (lhs.of_reg v_3109) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10402 0 32) 24 8) 53 11) 64) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10402 32 64) 24 8) 53 11) 64) (concat (Float2MInt (roundFloat (MInt2Float (extract v_10402 64 96) 24 8) 53 11) 64) (Float2MInt (roundFloat (MInt2Float (extract v_10402 96 128) 24 8) 53 11) 64))));
      pure ()
    pat_end
