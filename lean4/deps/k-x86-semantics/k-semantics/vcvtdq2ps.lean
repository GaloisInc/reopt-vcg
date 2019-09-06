def vcvtdq2ps1 : instruction :=
  definst "vcvtdq2ps" $ do
    pattern fun (v_3111 : reg (bv 128)) (v_3112 : reg (bv 128)) => do
      v_5779 <- getRegister v_3111;
      setRegister (lhs.of_reg v_3112) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5779 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5779 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5779 64 96)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_5779 96 128)) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_3117 : reg (bv 256)) (v_3118 : reg (bv 256)) => do
      v_5804 <- getRegister v_3117;
      setRegister (lhs.of_reg v_3118) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5804 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5804 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5804 64 96)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5804 96 128)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5804 128 160)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5804 160 192)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5804 192 224)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_5804 224 256)) 24 8) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3104 : Mem) (v_3107 : reg (bv 128)) => do
      v_9917 <- evaluateAddress v_3104;
      v_9918 <- load v_9917 16;
      setRegister (lhs.of_reg v_3107) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9918 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9918 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9918 64 96)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_9918 96 128)) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_3113 : Mem) (v_3114 : reg (bv 256)) => do
      v_9939 <- evaluateAddress v_3113;
      v_9940 <- load v_9939 32;
      setRegister (lhs.of_reg v_3114) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9940 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9940 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9940 64 96)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9940 96 128)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9940 128 160)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9940 160 192)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_9940 192 224)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_9940 224 256)) 24 8) 32))))))));
      pure ()
    pat_end
