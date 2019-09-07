def vcvtdq2pd1 : instruction :=
  definst "vcvtdq2pd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 8;
      setRegister (lhs.of_reg xmm_1) (concat (Float2MInt (Int2Float (svalueMInt (extract v_3 0 32)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_3 32 64)) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      setRegister (lhs.of_reg ymm_1) (concat (Float2MInt (Int2Float (svalueMInt (extract v_3 0 32)) 53 11) 64) (concat (Float2MInt (Int2Float (svalueMInt (extract v_3 32 64)) 53 11) 64) (concat (Float2MInt (Int2Float (svalueMInt (extract v_3 64 96)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_3 96 128)) 53 11) 64))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_0;
      setRegister (lhs.of_reg xmm_1) (concat (Float2MInt (Int2Float (svalueMInt (extract v_2 64 96)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_2 96 128)) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) => do
      v_2 <- getRegister ymm_0;
      setRegister (lhs.of_reg ymm_1) (concat (Float2MInt (Int2Float (svalueMInt (extract v_2 128 160)) 53 11) 64) (concat (Float2MInt (Int2Float (svalueMInt (extract v_2 160 192)) 53 11) 64) (concat (Float2MInt (Int2Float (svalueMInt (extract v_2 192 224)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_2 224 256)) 53 11) 64))));
      pure ()
    pat_end
