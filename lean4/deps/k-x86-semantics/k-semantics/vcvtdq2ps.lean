def vcvtdq2ps1 : instruction :=
  definst "vcvtdq2ps" $ do
    pattern fun (v_3033 : reg (bv 128)) (v_3034 : reg (bv 128)) => do
      v_6289 <- getRegister v_3033;
      setRegister (lhs.of_reg v_3034) (concat (Float2MInt (Int2Float (svalueMInt (extract v_6289 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_6289 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_6289 64 96)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_6289 96 128)) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_3039 : reg (bv 256)) (v_3040 : reg (bv 256)) => do
      v_6314 <- getRegister v_3039;
      setRegister (lhs.of_reg v_3040) (concat (Float2MInt (Int2Float (svalueMInt (extract v_6314 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_6314 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_6314 64 96)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_6314 96 128)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_6314 128 160)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_6314 160 192)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_6314 192 224)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_6314 224 256)) 24 8) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3026 : Mem) (v_3029 : reg (bv 128)) => do
      v_11670 <- evaluateAddress v_3026;
      v_11671 <- load v_11670 16;
      setRegister (lhs.of_reg v_3029) (concat (Float2MInt (Int2Float (svalueMInt (extract v_11671 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_11671 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_11671 64 96)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_11671 96 128)) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_3035 : Mem) (v_3036 : reg (bv 256)) => do
      v_11692 <- evaluateAddress v_3035;
      v_11693 <- load v_11692 32;
      setRegister (lhs.of_reg v_3036) (concat (Float2MInt (Int2Float (svalueMInt (extract v_11693 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_11693 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_11693 64 96)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_11693 96 128)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_11693 128 160)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_11693 160 192)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_11693 192 224)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_11693 224 256)) 24 8) 32))))))));
      pure ()
    pat_end
