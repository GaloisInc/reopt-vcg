def vcvtdq2ps1 : instruction :=
  definst "vcvtdq2ps" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      setRegister (lhs.of_reg xmm_1) (concat (Float2MInt (Int2Float (svalueMInt (extract v_3 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_3 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_3 64 96)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_3 96 128)) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 32;
      setRegister (lhs.of_reg ymm_1) (concat (Float2MInt (Int2Float (svalueMInt (extract v_3 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_3 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_3 64 96)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_3 96 128)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_3 128 160)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_3 160 192)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_3 192 224)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_3 224 256)) 24 8) 32))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_0;
      setRegister (lhs.of_reg xmm_1) (concat (Float2MInt (Int2Float (svalueMInt (extract v_2 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_2 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_2 64 96)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_2 96 128)) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) => do
      v_2 <- getRegister ymm_0;
      setRegister (lhs.of_reg ymm_1) (concat (Float2MInt (Int2Float (svalueMInt (extract v_2 0 32)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_2 32 64)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_2 64 96)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_2 96 128)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_2 128 160)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_2 160 192)) 24 8) 32) (concat (Float2MInt (Int2Float (svalueMInt (extract v_2 192 224)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_2 224 256)) 24 8) 32))))))));
      pure ()
    pat_end
