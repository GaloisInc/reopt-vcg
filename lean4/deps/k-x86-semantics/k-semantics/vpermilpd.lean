def vpermilpd : instruction :=
  definst "vpermilpd" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- evaluateAddress mem_1;
      v_5 <- load v_4 16;
      v_6 <- eval (extract v_5 64 128);
      v_7 <- eval (extract v_5 0 64);
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitClear v_3 6) v_6 v_7) (mux (isBitClear v_3 7) v_6 v_7));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- evaluateAddress mem_1;
      v_5 <- load v_4 32;
      v_6 <- eval (extract v_5 64 128);
      v_7 <- eval (extract v_5 0 64);
      v_8 <- eval (extract v_5 192 256);
      v_9 <- eval (extract v_5 128 192);
      setRegister (lhs.of_reg ymm_2) (concat (mux (isBitClear v_3 4) v_6 v_7) (concat (mux (isBitClear v_3 5) v_6 v_7) (concat (mux (isBitClear v_3 6) v_8 v_9) (mux (isBitClear v_3 7) v_8 v_9))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      v_5 <- eval (extract v_4 64 128);
      v_6 <- eval (extract v_4 0 64);
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitClear v_3 6) v_5 v_6) (mux (isBitClear v_3 7) v_5 v_6));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- getRegister (lhs.of_reg ymm_1);
      v_5 <- eval (extract v_4 64 128);
      v_6 <- eval (extract v_4 0 64);
      v_7 <- eval (extract v_4 192 256);
      v_8 <- eval (extract v_4 128 192);
      setRegister (lhs.of_reg ymm_2) (concat (mux (isBitClear v_3 4) v_5 v_6) (concat (mux (isBitClear v_3 5) v_5 v_6) (concat (mux (isBitClear v_3 6) v_7 v_8) (mux (isBitClear v_3 7) v_7 v_8))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      v_5 <- getRegister (lhs.of_reg xmm_1);
      v_6 <- eval (extract v_5 64 128);
      v_7 <- eval (extract v_5 0 64);
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitClear v_4 62) v_6 v_7) (mux (isBitClear v_4 126) v_6 v_7));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 32;
      v_5 <- getRegister (lhs.of_reg ymm_1);
      v_6 <- eval (extract v_5 64 128);
      v_7 <- eval (extract v_5 0 64);
      v_8 <- eval (extract v_5 192 256);
      v_9 <- eval (extract v_5 128 192);
      setRegister (lhs.of_reg ymm_2) (concat (mux (isBitClear v_4 62) v_6 v_7) (concat (mux (isBitClear v_4 126) v_6 v_7) (concat (mux (isBitClear v_4 190) v_8 v_9) (mux (isBitClear v_4 254) v_8 v_9))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_0);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      v_5 <- eval (extract v_4 64 128);
      v_6 <- eval (extract v_4 0 64);
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitClear v_3 62) v_5 v_6) (mux (isBitClear v_3 126) v_5 v_6));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_0);
      v_4 <- getRegister (lhs.of_reg ymm_1);
      v_5 <- eval (extract v_4 64 128);
      v_6 <- eval (extract v_4 0 64);
      v_7 <- eval (extract v_4 192 256);
      v_8 <- eval (extract v_4 128 192);
      setRegister (lhs.of_reg ymm_2) (concat (mux (isBitClear v_3 62) v_5 v_6) (concat (mux (isBitClear v_3 126) v_5 v_6) (concat (mux (isBitClear v_3 190) v_7 v_8) (mux (isBitClear v_3 254) v_7 v_8))));
      pure ()
    pat_end
