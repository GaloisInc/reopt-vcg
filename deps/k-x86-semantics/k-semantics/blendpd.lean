def blendpd : instruction :=
  definst "blendpd" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- getRegister (lhs.of_reg xmm_2);
      (v_5 : expression (bv 64)) <- eval (extract v_4 0 64);
      v_6 <- evaluateAddress mem_1;
      v_7 <- load v_6 16;
      (v_8 : expression (bv 64)) <- eval (extract v_7 0 64);
      (v_9 : expression (bv 64)) <- eval (extract v_4 64 128);
      (v_10 : expression (bv 64)) <- eval (extract v_7 64 128);
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitClear v_3 6) v_5 v_8) (mux (isBitClear v_3 7) v_9 v_10));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- getRegister (lhs.of_reg xmm_2);
      (v_5 : expression (bv 64)) <- eval (extract v_4 0 64);
      v_6 <- getRegister (lhs.of_reg xmm_1);
      (v_7 : expression (bv 64)) <- eval (extract v_6 0 64);
      (v_8 : expression (bv 64)) <- eval (extract v_4 64 128);
      (v_9 : expression (bv 64)) <- eval (extract v_6 64 128);
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitClear v_3 6) v_5 v_7) (mux (isBitClear v_3 7) v_8 v_9));
      pure ()
    pat_end
