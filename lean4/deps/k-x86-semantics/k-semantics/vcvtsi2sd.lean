def vcvtsi2sd : instruction :=
  definst "vcvtsi2sd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 4;
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 64) (Float2MInt (Int2Float (svalueMInt v_5) 53 11) 64));
      pure ()
    pat_end
