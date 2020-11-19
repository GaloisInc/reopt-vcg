def pslld : instruction :=
  definst "pslld" $ do
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) => do
      v_2 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- eval (concat (expression.bv_nat 24 0) v_2);
      (v_6 : expression (bv 32)) <- eval (extract (shl v_4 v_5) 0 32);
      (v_7 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_8 : expression (bv 32)) <- eval (extract (shl v_7 v_5) 0 32);
      (v_9 : expression (bv 32)) <- eval (extract v_3 64 96);
      (v_10 : expression (bv 32)) <- eval (extract (shl v_9 v_5) 0 32);
      (v_11 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_12 : expression (bv 32)) <- eval (extract (shl v_11 v_5) 0 32);
      setRegister (lhs.of_reg xmm_1) (mux (ugt (concat (expression.bv_nat 56 0) v_2) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat v_6 (concat v_8 (concat v_10 v_12))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      (v_7 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_8 : expression (bv 32)) <- eval (extract (shl v_6 v_7) 0 32);
      (v_9 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_10 : expression (bv 32)) <- eval (extract (shl v_9 v_7) 0 32);
      (v_11 : expression (bv 32)) <- eval (extract v_5 64 96);
      (v_12 : expression (bv 32)) <- eval (extract (shl v_11 v_7) 0 32);
      (v_13 : expression (bv 32)) <- eval (extract v_5 96 128);
      (v_14 : expression (bv 32)) <- eval (extract (shl v_13 v_7) 0 32);
      setRegister (lhs.of_reg xmm_1) (mux (ugt v_4 (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat v_8 (concat v_10 (concat v_12 v_14))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 64)) <- eval (extract v_2 64 128);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      (v_6 : expression (bv 32)) <- eval (extract v_2 96 128);
      (v_7 : expression (bv 32)) <- eval (extract (shl v_5 v_6) 0 32);
      (v_8 : expression (bv 32)) <- eval (extract v_4 32 64);
      (v_9 : expression (bv 32)) <- eval (extract (shl v_8 v_6) 0 32);
      (v_10 : expression (bv 32)) <- eval (extract v_4 64 96);
      (v_11 : expression (bv 32)) <- eval (extract (shl v_10 v_6) 0 32);
      (v_12 : expression (bv 32)) <- eval (extract v_4 96 128);
      (v_13 : expression (bv 32)) <- eval (extract (shl v_12 v_6) 0 32);
      setRegister (lhs.of_reg xmm_1) (mux (ugt v_3 (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat v_7 (concat v_9 (concat v_11 v_13))));
      pure ()
    pat_end
