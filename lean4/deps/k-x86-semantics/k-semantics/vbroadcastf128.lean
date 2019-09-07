def vbroadcastf1281 : instruction :=
  definst "vbroadcastf128" $ do
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      setRegister (lhs.of_reg ymm_1) (concat v_3 v_3);
      pure ()
    pat_end
