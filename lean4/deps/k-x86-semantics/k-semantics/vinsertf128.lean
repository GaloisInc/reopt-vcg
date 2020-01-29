def vinsertf128 : instruction :=
  definst "vinsertf128" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- getRegister (lhs.of_reg ymm_2);
      (v_5 : expression (bv 128)) <- eval (extract v_4 0 128);
      v_6 <- evaluateAddress mem_1;
      v_7 <- load v_6 16;
      (v_8 : expression (bv 128)) <- eval (extract v_4 128 256);
      setRegister (lhs.of_reg ymm_3) (mux (isBitClear (handleImmediateWithSignExtend imm_0 8 8) 7) (concat v_5 v_7) (concat v_7 v_8));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- getRegister (lhs.of_reg ymm_2);
      (v_5 : expression (bv 128)) <- eval (extract v_4 0 128);
      v_6 <- getRegister (lhs.of_reg xmm_1);
      (v_7 : expression (bv 128)) <- eval (extract v_4 128 256);
      setRegister (lhs.of_reg ymm_3) (mux (isBitClear (handleImmediateWithSignExtend imm_0 8 8) 7) (concat v_5 v_6) (concat v_6 v_7));
      pure ()
    pat_end
