def vcmpps : instruction :=
  definst "vcmpps" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister (lhs.of_reg xmm_2);
      (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      v_6 <- evaluateAddress mem_1;
      v_7 <- load v_6 16;
      (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      v_9 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      (v_10 : expression (bv 32)) <- eval (extract v_4 32 64);
      (v_11 : expression (bv 32)) <- eval (extract v_7 32 64);
      (v_12 : expression (bv 32)) <- eval (extract v_4 64 96);
      (v_13 : expression (bv 32)) <- eval (extract v_7 64 96);
      (v_14 : expression (bv 32)) <- eval (extract v_4 96 128);
      (v_15 : expression (bv 32)) <- eval (extract v_7 96 128);
      setRegister (lhs.of_reg xmm_3) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_5 v_8 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_10 v_11 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_12 v_13 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (/- (_,_,_) -/ cmp_single_pred v_14 v_15 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- getRegister (lhs.of_reg ymm_2);
      (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      v_6 <- evaluateAddress mem_1;
      v_7 <- load v_6 32;
      (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      v_9 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      (v_10 : expression (bv 32)) <- eval (extract v_4 32 64);
      (v_11 : expression (bv 32)) <- eval (extract v_7 32 64);
      (v_12 : expression (bv 32)) <- eval (extract v_4 64 96);
      (v_13 : expression (bv 32)) <- eval (extract v_7 64 96);
      (v_14 : expression (bv 32)) <- eval (extract v_4 96 128);
      (v_15 : expression (bv 32)) <- eval (extract v_7 96 128);
      (v_16 : expression (bv 32)) <- eval (extract v_4 128 160);
      (v_17 : expression (bv 32)) <- eval (extract v_7 128 160);
      (v_18 : expression (bv 32)) <- eval (extract v_4 160 192);
      (v_19 : expression (bv 32)) <- eval (extract v_7 160 192);
      (v_20 : expression (bv 32)) <- eval (extract v_4 192 224);
      (v_21 : expression (bv 32)) <- eval (extract v_7 192 224);
      (v_22 : expression (bv 32)) <- eval (extract v_4 224 256);
      (v_23 : expression (bv 32)) <- eval (extract v_7 224 256);
      setRegister (lhs.of_reg ymm_3) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_5 v_8 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_10 v_11 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_12 v_13 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_14 v_15 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_16 v_17 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_18 v_19 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_20 v_21 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (/- (_,_,_) -/ cmp_single_pred v_22 v_23 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister (lhs.of_reg xmm_2);
      (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      v_6 <- getRegister (lhs.of_reg xmm_1);
      (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      v_8 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      (v_9 : expression (bv 32)) <- eval (extract v_4 32 64);
      (v_10 : expression (bv 32)) <- eval (extract v_6 32 64);
      (v_11 : expression (bv 32)) <- eval (extract v_4 64 96);
      (v_12 : expression (bv 32)) <- eval (extract v_6 64 96);
      (v_13 : expression (bv 32)) <- eval (extract v_4 96 128);
      (v_14 : expression (bv 32)) <- eval (extract v_6 96 128);
      setRegister (lhs.of_reg xmm_3) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_5 v_7 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_9 v_10 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_11 v_12 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (/- (_,_,_) -/ cmp_single_pred v_13 v_14 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- getRegister (lhs.of_reg ymm_2);
      (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      v_6 <- getRegister (lhs.of_reg ymm_1);
      (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      v_8 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      (v_9 : expression (bv 32)) <- eval (extract v_4 32 64);
      (v_10 : expression (bv 32)) <- eval (extract v_6 32 64);
      (v_11 : expression (bv 32)) <- eval (extract v_4 64 96);
      (v_12 : expression (bv 32)) <- eval (extract v_6 64 96);
      (v_13 : expression (bv 32)) <- eval (extract v_4 96 128);
      (v_14 : expression (bv 32)) <- eval (extract v_6 96 128);
      (v_15 : expression (bv 32)) <- eval (extract v_4 128 160);
      (v_16 : expression (bv 32)) <- eval (extract v_6 128 160);
      (v_17 : expression (bv 32)) <- eval (extract v_4 160 192);
      (v_18 : expression (bv 32)) <- eval (extract v_6 160 192);
      (v_19 : expression (bv 32)) <- eval (extract v_4 192 224);
      (v_20 : expression (bv 32)) <- eval (extract v_6 192 224);
      (v_21 : expression (bv 32)) <- eval (extract v_4 224 256);
      (v_22 : expression (bv 32)) <- eval (extract v_6 224 256);
      setRegister (lhs.of_reg ymm_3) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_5 v_7 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_9 v_10 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_11 v_12 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_13 v_14 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_15 v_16 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_17 v_18 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_19 v_20 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (/- (_,_,_) -/ cmp_single_pred v_21 v_22 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end
