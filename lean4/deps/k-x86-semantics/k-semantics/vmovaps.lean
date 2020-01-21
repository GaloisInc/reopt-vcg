def vmovaps : instruction :=
  definst "vmovaps" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      setRegister (lhs.of_reg xmm_1) v_3;
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 32;
      setRegister (lhs.of_reg ymm_1) v_3;
      pure ()
    pat_end;
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
