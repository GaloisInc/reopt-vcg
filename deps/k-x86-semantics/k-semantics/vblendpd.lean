def vblendpd : instruction :=
  definst "vblendpd" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- getRegister (lhs.of_reg xmm_2);
      (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      v_7 <- evaluateAddress mem_1;
      v_8 <- load v_7 16;
      (v_9 : expression (bv 64)) <- eval (extract v_8 0 64);
      (v_10 : expression (bv 64)) <- eval (extract v_5 64 128);
      (v_11 : expression (bv 64)) <- eval (extract v_8 64 128);
      setRegister (lhs.of_reg xmm_3) (concat (mux (isBitClear v_4 6) v_6 v_9) (mux (isBitClear v_4 7) v_10 v_11));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- getRegister (lhs.of_reg ymm_2);
      (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      v_7 <- evaluateAddress mem_1;
      v_8 <- load v_7 32;
      (v_9 : expression (bv 64)) <- eval (extract v_8 0 64);
      (v_10 : expression (bv 64)) <- eval (extract v_5 64 128);
      (v_11 : expression (bv 64)) <- eval (extract v_8 64 128);
      (v_12 : expression (bv 64)) <- eval (extract v_5 128 192);
      (v_13 : expression (bv 64)) <- eval (extract v_8 128 192);
      (v_14 : expression (bv 64)) <- eval (extract v_5 192 256);
      (v_15 : expression (bv 64)) <- eval (extract v_8 192 256);
      setRegister (lhs.of_reg ymm_3) (concat (mux (isBitClear v_4 4) v_6 v_9) (concat (mux (isBitClear v_4 5) v_10 v_11) (concat (mux (isBitClear v_4 6) v_12 v_13) (mux (isBitClear v_4 7) v_14 v_15))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- getRegister (lhs.of_reg xmm_2);
      (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      v_7 <- getRegister (lhs.of_reg xmm_1);
      (v_8 : expression (bv 64)) <- eval (extract v_7 0 64);
      (v_9 : expression (bv 64)) <- eval (extract v_5 64 128);
      (v_10 : expression (bv 64)) <- eval (extract v_7 64 128);
      setRegister (lhs.of_reg xmm_3) (concat (mux (isBitClear v_4 6) v_6 v_8) (mux (isBitClear v_4 7) v_9 v_10));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- getRegister (lhs.of_reg ymm_2);
      (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      v_7 <- getRegister (lhs.of_reg ymm_1);
      (v_8 : expression (bv 64)) <- eval (extract v_7 0 64);
      (v_9 : expression (bv 64)) <- eval (extract v_5 64 128);
      (v_10 : expression (bv 64)) <- eval (extract v_7 64 128);
      (v_11 : expression (bv 64)) <- eval (extract v_5 128 192);
      (v_12 : expression (bv 64)) <- eval (extract v_7 128 192);
      (v_13 : expression (bv 64)) <- eval (extract v_5 192 256);
      (v_14 : expression (bv 64)) <- eval (extract v_7 192 256);
      setRegister (lhs.of_reg ymm_3) (concat (mux (isBitClear v_4 4) v_6 v_8) (concat (mux (isBitClear v_4 5) v_9 v_10) (concat (mux (isBitClear v_4 6) v_11 v_12) (mux (isBitClear v_4 7) v_13 v_14))));
      pure ()
    pat_end
