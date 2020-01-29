def blendps : instruction :=
  definst "blendps" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- getRegister (lhs.of_reg xmm_2);
      (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      v_6 <- evaluateAddress mem_1;
      v_7 <- load v_6 16;
      (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      (v_9 : expression (bv 32)) <- eval (extract v_4 32 64);
      (v_10 : expression (bv 32)) <- eval (extract v_7 32 64);
      (v_11 : expression (bv 32)) <- eval (extract v_4 64 96);
      (v_12 : expression (bv 32)) <- eval (extract v_7 64 96);
      (v_13 : expression (bv 32)) <- eval (extract v_4 96 128);
      (v_14 : expression (bv 32)) <- eval (extract v_7 96 128);
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitClear v_3 4) v_5 v_8) (concat (mux (isBitClear v_3 5) v_9 v_10) (concat (mux (isBitClear v_3 6) v_11 v_12) (mux (isBitClear v_3 7) v_13 v_14))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- getRegister (lhs.of_reg xmm_2);
      (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      v_6 <- getRegister (lhs.of_reg xmm_1);
      (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      (v_8 : expression (bv 32)) <- eval (extract v_4 32 64);
      (v_9 : expression (bv 32)) <- eval (extract v_6 32 64);
      (v_10 : expression (bv 32)) <- eval (extract v_4 64 96);
      (v_11 : expression (bv 32)) <- eval (extract v_6 64 96);
      (v_12 : expression (bv 32)) <- eval (extract v_4 96 128);
      (v_13 : expression (bv 32)) <- eval (extract v_6 96 128);
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitClear v_3 4) v_5 v_7) (concat (mux (isBitClear v_3 5) v_8 v_9) (concat (mux (isBitClear v_3 6) v_10 v_11) (mux (isBitClear v_3 7) v_12 v_13))));
      pure ()
    pat_end
