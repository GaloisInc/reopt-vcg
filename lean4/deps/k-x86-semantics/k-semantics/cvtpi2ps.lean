def cvtpi2ps : instruction :=
  definst "cvtpi2ps" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 8;
      setRegister (lhs.of_reg xmm_1) (concat (extract v_2 0 64) (concat (Float2MInt (Int2Float (svalueMInt (extract v_4 0 32)) 24 8) 32) (Float2MInt (Int2Float (svalueMInt (extract v_4 32 64)) 24 8) 32)));
      pure ()
    pat_end
