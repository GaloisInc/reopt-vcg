def vmaxpd : instruction :=
  definst "vmaxpd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 16;
      (v_7 : expression (bv 64)) <- eval (extract v_6 0 64);
      (v_8 : expression (bv 64)) <- eval (extract v_3 64 128);
      (v_9 : expression (bv 64)) <- eval (extract v_6 64 128);
      setRegister (lhs.of_reg xmm_2) (concat (mux (eq (/- (_,_) -/  maxcmp_double v_4 v_7) (expression.bv_nat 1 1)) v_4 v_7) (mux (eq (/- (_,_) -/  maxcmp_double v_8 v_9) (expression.bv_nat 1 1)) v_8 v_9));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 32;
      (v_7 : expression (bv 64)) <- eval (extract v_6 0 64);
      (v_8 : expression (bv 64)) <- eval (extract v_3 64 128);
      (v_9 : expression (bv 64)) <- eval (extract v_6 64 128);
      (v_10 : expression (bv 64)) <- eval (extract v_3 128 192);
      (v_11 : expression (bv 64)) <- eval (extract v_6 128 192);
      (v_12 : expression (bv 64)) <- eval (extract v_3 192 256);
      (v_13 : expression (bv 64)) <- eval (extract v_6 192 256);
      setRegister (lhs.of_reg ymm_2) (concat (mux (eq (/- (_,_) -/  maxcmp_double v_4 v_7) (expression.bv_nat 1 1)) v_4 v_7) (concat (mux (eq (/- (_,_) -/  maxcmp_double v_8 v_9) (expression.bv_nat 1 1)) v_8 v_9) (concat (mux (eq (/- (_,_) -/  maxcmp_double v_10 v_11) (expression.bv_nat 1 1)) v_10 v_11) (mux (eq (/- (_,_) -/  maxcmp_double v_12 v_13) (expression.bv_nat 1 1)) v_12 v_13))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- getRegister (lhs.of_reg xmm_0);
      (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      (v_7 : expression (bv 64)) <- eval (extract v_3 64 128);
      (v_8 : expression (bv 64)) <- eval (extract v_5 64 128);
      setRegister (lhs.of_reg xmm_2) (concat (mux (eq (/- (_,_) -/  maxcmp_double v_4 v_6) (expression.bv_nat 1 1)) v_4 v_6) (mux (eq (/- (_,_) -/  maxcmp_double v_7 v_8) (expression.bv_nat 1 1)) v_7 v_8));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- getRegister (lhs.of_reg ymm_0);
      (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      (v_7 : expression (bv 64)) <- eval (extract v_3 64 128);
      (v_8 : expression (bv 64)) <- eval (extract v_5 64 128);
      (v_9 : expression (bv 64)) <- eval (extract v_3 128 192);
      (v_10 : expression (bv 64)) <- eval (extract v_5 128 192);
      (v_11 : expression (bv 64)) <- eval (extract v_3 192 256);
      (v_12 : expression (bv 64)) <- eval (extract v_5 192 256);
      setRegister (lhs.of_reg ymm_2) (concat (mux (eq (/- (_,_) -/  maxcmp_double v_4 v_6) (expression.bv_nat 1 1)) v_4 v_6) (concat (mux (eq (/- (_,_) -/  maxcmp_double v_7 v_8) (expression.bv_nat 1 1)) v_7 v_8) (concat (mux (eq (/- (_,_) -/  maxcmp_double v_9 v_10) (expression.bv_nat 1 1)) v_9 v_10) (mux (eq (/- (_,_) -/  maxcmp_double v_11 v_12) (expression.bv_nat 1 1)) v_11 v_12))));
      pure ()
    pat_end
