def vcvtdq2ps1 : instruction :=
  definst "vcvtdq2ps" $ do
    pattern fun (v_3020 : reg (bv 128)) (v_3021 : reg (bv 128)) => do
      v_5830 <- getRegister v_3020;
      setRegister (lhs.of_reg v_3021) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5830 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5830 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5830 64 96)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_5830 96 128)) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_3027 : reg (bv 256)) (v_3028 : reg (bv 256)) => do
      v_5855 <- getRegister v_3027;
      setRegister (lhs.of_reg v_3028) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5855 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5855 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5855 64 96)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5855 96 128)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5855 128 160)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5855 160 192)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5855 192 224)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_5855 224 256)) 24 8) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3013 : Mem) (v_3016 : reg (bv 128)) => do
      v_10128 <- evaluateAddress v_3013;
      v_10129 <- load v_10128 16;
      setRegister (lhs.of_reg v_3016) (concat (Float2MInt (Int2Float (svalueMInt (extract v_10129 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_10129 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_10129 64 96)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_10129 96 128)) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_3022 : Mem) (v_3023 : reg (bv 256)) => do
      v_10150 <- evaluateAddress v_3022;
      v_10151 <- load v_10150 32;
      setRegister (lhs.of_reg v_3023) (concat (Float2MInt (Int2Float (svalueMInt (extract v_10151 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_10151 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_10151 64 96)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_10151 96 128)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_10151 128 160)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_10151 160 192)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_10151 192 224)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_10151 224 256)) 24 8) 32))))))));
      pure ()
    pat_end
