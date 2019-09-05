def vcvtdq2ps1 : instruction :=
  definst "vcvtdq2ps" $ do
    pattern fun (v_3084 : reg (bv 128)) (v_3085 : reg (bv 128)) => do
      v_5752 <- getRegister v_3084;
      setRegister (lhs.of_reg v_3085) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5752 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5752 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5752 64 96)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_5752 96 128)) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_3092 : reg (bv 256)) (v_3093 : reg (bv 256)) => do
      v_5777 <- getRegister v_3092;
      setRegister (lhs.of_reg v_3093) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5777 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5777 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5777 64 96)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5777 96 128)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5777 128 160)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5777 160 192)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5777 192 224)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_5777 224 256)) 24 8) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3079 : Mem) (v_3080 : reg (bv 128)) => do
      v_9890 <- evaluateAddress v_3079;
      v_9891 <- load v_9890 16;
      setRegister (lhs.of_reg v_3080) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9891 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9891 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9891 64 96)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_9891 96 128)) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_3088 : Mem) (v_3089 : reg (bv 256)) => do
      v_9912 <- evaluateAddress v_3088;
      v_9913 <- load v_9912 32;
      setRegister (lhs.of_reg v_3089) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9913 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9913 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9913 64 96)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9913 96 128)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9913 128 160)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9913 160 192)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9913 192 224)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_9913 224 256)) 24 8) 32))))))));
      pure ()
    pat_end
