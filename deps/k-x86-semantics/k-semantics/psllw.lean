def psllw : instruction :=
  definst "psllw" $ do
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) => do
      v_2 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      v_5 <- eval (concat (expression.bv_nat 8 0) v_2);
      (v_6 : expression (bv 16)) <- eval (extract (shl v_4 v_5) 0 16);
      (v_7 : expression (bv 16)) <- eval (extract v_3 16 32);
      (v_8 : expression (bv 16)) <- eval (extract (shl v_7 v_5) 0 16);
      (v_9 : expression (bv 16)) <- eval (extract v_3 32 48);
      (v_10 : expression (bv 16)) <- eval (extract (shl v_9 v_5) 0 16);
      (v_11 : expression (bv 16)) <- eval (extract v_3 48 64);
      (v_12 : expression (bv 16)) <- eval (extract (shl v_11 v_5) 0 16);
      (v_13 : expression (bv 16)) <- eval (extract v_3 64 80);
      (v_14 : expression (bv 16)) <- eval (extract (shl v_13 v_5) 0 16);
      (v_15 : expression (bv 16)) <- eval (extract v_3 80 96);
      (v_16 : expression (bv 16)) <- eval (extract (shl v_15 v_5) 0 16);
      (v_17 : expression (bv 16)) <- eval (extract v_3 96 112);
      (v_18 : expression (bv 16)) <- eval (extract (shl v_17 v_5) 0 16);
      (v_19 : expression (bv 16)) <- eval (extract v_3 112 128);
      (v_20 : expression (bv 16)) <- eval (extract (shl v_19 v_5) 0 16);
      setRegister (lhs.of_reg xmm_1) (mux (ugt (concat (expression.bv_nat 56 0) v_2) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat v_6 (concat v_8 (concat v_10 (concat v_12 (concat v_14 (concat v_16 (concat v_18 v_20))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      (v_7 : expression (bv 16)) <- eval (extract v_3 112 128);
      (v_8 : expression (bv 16)) <- eval (extract (shl v_6 v_7) 0 16);
      (v_9 : expression (bv 16)) <- eval (extract v_5 16 32);
      (v_10 : expression (bv 16)) <- eval (extract (shl v_9 v_7) 0 16);
      (v_11 : expression (bv 16)) <- eval (extract v_5 32 48);
      (v_12 : expression (bv 16)) <- eval (extract (shl v_11 v_7) 0 16);
      (v_13 : expression (bv 16)) <- eval (extract v_5 48 64);
      (v_14 : expression (bv 16)) <- eval (extract (shl v_13 v_7) 0 16);
      (v_15 : expression (bv 16)) <- eval (extract v_5 64 80);
      (v_16 : expression (bv 16)) <- eval (extract (shl v_15 v_7) 0 16);
      (v_17 : expression (bv 16)) <- eval (extract v_5 80 96);
      (v_18 : expression (bv 16)) <- eval (extract (shl v_17 v_7) 0 16);
      (v_19 : expression (bv 16)) <- eval (extract v_5 96 112);
      (v_20 : expression (bv 16)) <- eval (extract (shl v_19 v_7) 0 16);
      (v_21 : expression (bv 16)) <- eval (extract v_5 112 128);
      (v_22 : expression (bv 16)) <- eval (extract (shl v_21 v_7) 0 16);
      setRegister (lhs.of_reg xmm_1) (mux (ugt v_4 (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat v_8 (concat v_10 (concat v_12 (concat v_14 (concat v_16 (concat v_18 (concat v_20 v_22))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 64)) <- eval (extract v_2 64 128);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      (v_5 : expression (bv 16)) <- eval (extract v_4 0 16);
      (v_6 : expression (bv 16)) <- eval (extract v_2 112 128);
      (v_7 : expression (bv 16)) <- eval (extract (shl v_5 v_6) 0 16);
      (v_8 : expression (bv 16)) <- eval (extract v_4 16 32);
      (v_9 : expression (bv 16)) <- eval (extract (shl v_8 v_6) 0 16);
      (v_10 : expression (bv 16)) <- eval (extract v_4 32 48);
      (v_11 : expression (bv 16)) <- eval (extract (shl v_10 v_6) 0 16);
      (v_12 : expression (bv 16)) <- eval (extract v_4 48 64);
      (v_13 : expression (bv 16)) <- eval (extract (shl v_12 v_6) 0 16);
      (v_14 : expression (bv 16)) <- eval (extract v_4 64 80);
      (v_15 : expression (bv 16)) <- eval (extract (shl v_14 v_6) 0 16);
      (v_16 : expression (bv 16)) <- eval (extract v_4 80 96);
      (v_17 : expression (bv 16)) <- eval (extract (shl v_16 v_6) 0 16);
      (v_18 : expression (bv 16)) <- eval (extract v_4 96 112);
      (v_19 : expression (bv 16)) <- eval (extract (shl v_18 v_6) 0 16);
      (v_20 : expression (bv 16)) <- eval (extract v_4 112 128);
      (v_21 : expression (bv 16)) <- eval (extract (shl v_20 v_6) 0 16);
      setRegister (lhs.of_reg xmm_1) (mux (ugt v_3 (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat v_7 (concat v_9 (concat v_11 (concat v_13 (concat v_15 (concat v_17 (concat v_19 v_21))))))));
      pure ()
    pat_end
