def vmovd : instruction :=
  definst "vmovd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 4;
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 96 0) (concat (extract v_3 0 8) (extract v_3 8 32)));
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg r32_0);
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 96 0) (concat (extract v_2 0 8) (extract v_2 8 32)));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister (lhs.of_reg xmm_0);
      store v_2 (extract v_3 96 128) 4;
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg r32_1) (extract v_2 96 128);
      pure ()
    pat_end
