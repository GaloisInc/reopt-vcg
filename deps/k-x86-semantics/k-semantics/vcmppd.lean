def vcmppd : instruction :=
  definst "vcmppd" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister (lhs.of_reg xmm_2);
      (v_5 : expression (bv 64)) <- eval (extract v_4 0 64);
      v_6 <- evaluateAddress mem_1;
      v_7 <- load v_6 16;
      (v_8 : expression (bv 64)) <- eval (extract v_7 0 64);
      v_9 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      (v_10 : expression (bv 64)) <- eval (extract v_4 64 128);
      (v_11 : expression (bv 64)) <- eval (extract v_7 64 128);
      setRegister (lhs.of_reg xmm_3) (concat (mux (eq (/- (_,_,_) -/ cmp_double_pred v_5 v_8 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (/- (_,_,_) -/ cmp_double_pred v_10 v_11 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- getRegister (lhs.of_reg ymm_2);
      (v_5 : expression (bv 64)) <- eval (extract v_4 0 64);
      v_6 <- evaluateAddress mem_1;
      v_7 <- load v_6 32;
      (v_8 : expression (bv 64)) <- eval (extract v_7 0 64);
      v_9 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      (v_10 : expression (bv 64)) <- eval (extract v_4 64 128);
      (v_11 : expression (bv 64)) <- eval (extract v_7 64 128);
      (v_12 : expression (bv 64)) <- eval (extract v_4 128 192);
      (v_13 : expression (bv 64)) <- eval (extract v_7 128 192);
      (v_14 : expression (bv 64)) <- eval (extract v_4 192 256);
      (v_15 : expression (bv 64)) <- eval (extract v_7 192 256);
      setRegister (lhs.of_reg ymm_3) (concat (mux (eq (/- (_,_,_) -/ cmp_double_pred v_5 v_8 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_double_pred v_10 v_11 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_double_pred v_12 v_13 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (/- (_,_,_) -/ cmp_double_pred v_14 v_15 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister (lhs.of_reg xmm_2);
      (v_5 : expression (bv 64)) <- eval (extract v_4 0 64);
      v_6 <- getRegister (lhs.of_reg xmm_1);
      (v_7 : expression (bv 64)) <- eval (extract v_6 0 64);
      v_8 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      (v_9 : expression (bv 64)) <- eval (extract v_4 64 128);
      (v_10 : expression (bv 64)) <- eval (extract v_6 64 128);
      setRegister (lhs.of_reg xmm_3) (concat (mux (eq (/- (_,_,_) -/ cmp_double_pred v_5 v_7 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (/- (_,_,_) -/ cmp_double_pred v_9 v_10 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- getRegister (lhs.of_reg ymm_2);
      (v_5 : expression (bv 64)) <- eval (extract v_4 0 64);
      v_6 <- getRegister (lhs.of_reg ymm_1);
      (v_7 : expression (bv 64)) <- eval (extract v_6 0 64);
      v_8 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      (v_9 : expression (bv 64)) <- eval (extract v_4 64 128);
      (v_10 : expression (bv 64)) <- eval (extract v_6 64 128);
      (v_11 : expression (bv 64)) <- eval (extract v_4 128 192);
      (v_12 : expression (bv 64)) <- eval (extract v_6 128 192);
      (v_13 : expression (bv 64)) <- eval (extract v_4 192 256);
      (v_14 : expression (bv 64)) <- eval (extract v_6 192 256);
      setRegister (lhs.of_reg ymm_3) (concat (mux (eq (/- (_,_,_) -/ cmp_double_pred v_5 v_7 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_double_pred v_9 v_10 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (/- (_,_,_) -/ cmp_double_pred v_11 v_12 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (/- (_,_,_) -/ cmp_double_pred v_13 v_14 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end
