def vextracti128 : instruction :=
  definst "vextracti128" $ do
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (mem_2 : Mem) => do
      v_3 <- evaluateAddress mem_2;
      v_4 <- getRegister (lhs.of_reg ymm_1);
      (v_5 : expression (bv 128)) <- eval (extract v_4 128 256);
      (v_6 : expression (bv 128)) <- eval (extract v_4 0 128);
      store v_3 (mux (isBitClear (handleImmediateWithSignExtend imm_0 8 8) 7) v_5 v_6) 16;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 128)) <- eval (extract v_3 128 256);
      (v_5 : expression (bv 128)) <- eval (extract v_3 0 128);
      setRegister (lhs.of_reg xmm_2) (mux (isBitClear (handleImmediateWithSignExtend imm_0 8 8) 7) v_4 v_5);
      pure ()
    pat_end
