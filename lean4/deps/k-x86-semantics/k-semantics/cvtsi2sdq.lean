def cvtsi2sdq1 : instruction :=
  definst "cvtsi2sdq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 8;
      setRegister (lhs.of_reg xmm_1) (concat (extract v_2 0 64) (Float2MInt (Int2Float (svalueMInt v_4) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- getRegister r64_0;
      setRegister (lhs.of_reg xmm_1) (concat (extract v_2 0 64) (Float2MInt (Int2Float (svalueMInt v_3) 53 11) 64));
      pure ()
    pat_end
