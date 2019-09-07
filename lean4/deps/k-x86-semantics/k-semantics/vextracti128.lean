def vextracti1281 : instruction :=
  definst "vextracti128" $ do
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (mem_2 : Mem) => do
      v_3 <- evaluateAddress mem_2;
      v_4 <- getRegister ymm_1;
      store v_3 (mux (isBitClear (handleImmediateWithSignExtend imm_0 8 8) 7) (extract v_4 128 256) (extract v_4 0 128)) 16;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister ymm_1;
      setRegister (lhs.of_reg xmm_2) (mux (isBitClear (handleImmediateWithSignExtend imm_0 8 8) 7) (extract v_3 128 256) (extract v_3 0 128));
      pure ()
    pat_end
