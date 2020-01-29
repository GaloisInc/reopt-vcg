def packusdw : instruction :=
  definst "packusdw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      (v_5 : expression (bv 16)) <- eval (extract v_3 16 32);
      (v_6 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_7 : expression (bv 16)) <- eval (extract v_3 48 64);
      (v_8 : expression (bv 32)) <- eval (extract v_3 64 96);
      (v_9 : expression (bv 16)) <- eval (extract v_3 80 96);
      (v_10 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_11 : expression (bv 16)) <- eval (extract v_3 112 128);
      v_12 <- getRegister (lhs.of_reg xmm_1);
      (v_13 : expression (bv 32)) <- eval (extract v_12 0 32);
      (v_14 : expression (bv 16)) <- eval (extract v_12 16 32);
      (v_15 : expression (bv 32)) <- eval (extract v_12 32 64);
      (v_16 : expression (bv 16)) <- eval (extract v_12 48 64);
      (v_17 : expression (bv 32)) <- eval (extract v_12 64 96);
      (v_18 : expression (bv 16)) <- eval (extract v_12 80 96);
      (v_19 : expression (bv 32)) <- eval (extract v_12 96 128);
      (v_20 : expression (bv 16)) <- eval (extract v_12 112 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_4 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_4 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_5)) (concat (mux (sgt v_6 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_7)) (concat (mux (sgt v_8 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_8 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_9)) (concat (mux (sgt v_10 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_10 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_11)) (concat (mux (sgt v_13 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_13 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_14)) (concat (mux (sgt v_15 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_15 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_16)) (concat (mux (sgt v_17 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_17 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_18)) (mux (sgt v_19 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_19 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_20)))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      (v_4 : expression (bv 16)) <- eval (extract v_2 16 32);
      (v_5 : expression (bv 32)) <- eval (extract v_2 32 64);
      (v_6 : expression (bv 16)) <- eval (extract v_2 48 64);
      (v_7 : expression (bv 32)) <- eval (extract v_2 64 96);
      (v_8 : expression (bv 16)) <- eval (extract v_2 80 96);
      (v_9 : expression (bv 32)) <- eval (extract v_2 96 128);
      (v_10 : expression (bv 16)) <- eval (extract v_2 112 128);
      v_11 <- getRegister (lhs.of_reg xmm_1);
      (v_12 : expression (bv 32)) <- eval (extract v_11 0 32);
      (v_13 : expression (bv 16)) <- eval (extract v_11 16 32);
      (v_14 : expression (bv 32)) <- eval (extract v_11 32 64);
      (v_15 : expression (bv 16)) <- eval (extract v_11 48 64);
      (v_16 : expression (bv 32)) <- eval (extract v_11 64 96);
      (v_17 : expression (bv 16)) <- eval (extract v_11 80 96);
      (v_18 : expression (bv 32)) <- eval (extract v_11 96 128);
      (v_19 : expression (bv 16)) <- eval (extract v_11 112 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_3 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_3 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_4)) (concat (mux (sgt v_5 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_6)) (concat (mux (sgt v_7 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_8)) (concat (mux (sgt v_9 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_10)) (concat (mux (sgt v_12 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_13)) (concat (mux (sgt v_14 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_14 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_15)) (concat (mux (sgt v_16 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_16 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_17)) (mux (sgt v_18 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_18 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_19)))))))));
      pure ()
    pat_end
