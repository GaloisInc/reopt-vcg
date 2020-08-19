def phaddsw : instruction :=
  definst "phaddsw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      (v_5 : expression (bv 16)) <- eval (extract v_3 16 32);
      v_6 <- eval (add (sext v_4 32) (sext v_5 32));
      (v_7 : expression (bv 16)) <- eval (extract v_6 16 32);
      (v_8 : expression (bv 16)) <- eval (extract v_3 32 48);
      (v_9 : expression (bv 16)) <- eval (extract v_3 48 64);
      v_10 <- eval (add (sext v_8 32) (sext v_9 32));
      (v_11 : expression (bv 16)) <- eval (extract v_10 16 32);
      (v_12 : expression (bv 16)) <- eval (extract v_3 64 80);
      (v_13 : expression (bv 16)) <- eval (extract v_3 80 96);
      v_14 <- eval (add (sext v_12 32) (sext v_13 32));
      (v_15 : expression (bv 16)) <- eval (extract v_14 16 32);
      (v_16 : expression (bv 16)) <- eval (extract v_3 96 112);
      (v_17 : expression (bv 16)) <- eval (extract v_3 112 128);
      v_18 <- eval (add (sext v_16 32) (sext v_17 32));
      (v_19 : expression (bv 16)) <- eval (extract v_18 16 32);
      v_20 <- getRegister (lhs.of_reg xmm_1);
      (v_21 : expression (bv 16)) <- eval (extract v_20 0 16);
      (v_22 : expression (bv 16)) <- eval (extract v_20 16 32);
      v_23 <- eval (add (sext v_21 32) (sext v_22 32));
      (v_24 : expression (bv 16)) <- eval (extract v_23 16 32);
      (v_25 : expression (bv 16)) <- eval (extract v_20 32 48);
      (v_26 : expression (bv 16)) <- eval (extract v_20 48 64);
      v_27 <- eval (add (sext v_25 32) (sext v_26 32));
      (v_28 : expression (bv 16)) <- eval (extract v_27 16 32);
      (v_29 : expression (bv 16)) <- eval (extract v_20 64 80);
      (v_30 : expression (bv 16)) <- eval (extract v_20 80 96);
      v_31 <- eval (add (sext v_29 32) (sext v_30 32));
      (v_32 : expression (bv 16)) <- eval (extract v_31 16 32);
      (v_33 : expression (bv 16)) <- eval (extract v_20 112 128);
      (v_34 : expression (bv 16)) <- eval (extract v_20 96 112);
      v_35 <- eval (add (sext v_33 32) (sext v_34 32));
      (v_36 : expression (bv 16)) <- eval (extract v_35 16 32);
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_6 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_7)) (concat (mux (sgt v_10 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_11)) (concat (mux (sgt v_14 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_14 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_15)) (concat (mux (sgt v_18 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_19)) (concat (mux (sgt v_23 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_23 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_24)) (concat (mux (sgt v_27 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_27 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_28)) (concat (mux (sgt v_31 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_31 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_32)) (mux (sgt v_35 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_35 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_36)))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      (v_4 : expression (bv 16)) <- eval (extract v_2 16 32);
      v_5 <- eval (add (sext v_3 32) (sext v_4 32));
      (v_6 : expression (bv 16)) <- eval (extract v_5 16 32);
      (v_7 : expression (bv 16)) <- eval (extract v_2 32 48);
      (v_8 : expression (bv 16)) <- eval (extract v_2 48 64);
      v_9 <- eval (add (sext v_7 32) (sext v_8 32));
      (v_10 : expression (bv 16)) <- eval (extract v_9 16 32);
      (v_11 : expression (bv 16)) <- eval (extract v_2 64 80);
      (v_12 : expression (bv 16)) <- eval (extract v_2 80 96);
      v_13 <- eval (add (sext v_11 32) (sext v_12 32));
      (v_14 : expression (bv 16)) <- eval (extract v_13 16 32);
      (v_15 : expression (bv 16)) <- eval (extract v_2 96 112);
      (v_16 : expression (bv 16)) <- eval (extract v_2 112 128);
      v_17 <- eval (add (sext v_15 32) (sext v_16 32));
      (v_18 : expression (bv 16)) <- eval (extract v_17 16 32);
      v_19 <- getRegister (lhs.of_reg xmm_1);
      (v_20 : expression (bv 16)) <- eval (extract v_19 0 16);
      (v_21 : expression (bv 16)) <- eval (extract v_19 16 32);
      v_22 <- eval (add (sext v_20 32) (sext v_21 32));
      (v_23 : expression (bv 16)) <- eval (extract v_22 16 32);
      (v_24 : expression (bv 16)) <- eval (extract v_19 32 48);
      (v_25 : expression (bv 16)) <- eval (extract v_19 48 64);
      v_26 <- eval (add (sext v_24 32) (sext v_25 32));
      (v_27 : expression (bv 16)) <- eval (extract v_26 16 32);
      (v_28 : expression (bv 16)) <- eval (extract v_19 64 80);
      (v_29 : expression (bv 16)) <- eval (extract v_19 80 96);
      v_30 <- eval (add (sext v_28 32) (sext v_29 32));
      (v_31 : expression (bv 16)) <- eval (extract v_30 16 32);
      (v_32 : expression (bv 16)) <- eval (extract v_19 112 128);
      (v_33 : expression (bv 16)) <- eval (extract v_19 96 112);
      v_34 <- eval (add (sext v_32 32) (sext v_33 32));
      (v_35 : expression (bv 16)) <- eval (extract v_34 16 32);
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_5 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_6)) (concat (mux (sgt v_9 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_10)) (concat (mux (sgt v_13 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_14)) (concat (mux (sgt v_17 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_18)) (concat (mux (sgt v_22 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_22 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_23)) (concat (mux (sgt v_26 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_26 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_27)) (concat (mux (sgt v_30 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_30 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_31)) (mux (sgt v_34 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_34 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_35)))))))));
      pure ()
    pat_end