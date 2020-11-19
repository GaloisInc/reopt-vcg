def vmovntps : instruction :=
  definst "vmovntps" $ do
    pattern fun (xmm_0 : reg (bv 128)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister (lhs.of_reg xmm_0);
      store v_2 v_3 16;
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister (lhs.of_reg ymm_0);
      store v_2 v_3 32;
      pure ()
    pat_end
