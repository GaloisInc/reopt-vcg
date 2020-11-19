def psubusw : instruction :=
  definst "psubusw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 16;
      (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      v_7 <- eval (sub (concat (expression.bv_nat 2 0) v_3) (concat (expression.bv_nat 2 0) v_6));
      (v_8 : expression (bv 16)) <- eval (extract v_7 2 18);
      (v_9 : expression (bv 16)) <- eval (extract v_2 16 32);
      (v_10 : expression (bv 16)) <- eval (extract v_5 16 32);
      v_11 <- eval (sub (concat (expression.bv_nat 2 0) v_9) (concat (expression.bv_nat 2 0) v_10));
      (v_12 : expression (bv 16)) <- eval (extract v_11 2 18);
      (v_13 : expression (bv 16)) <- eval (extract v_2 32 48);
      (v_14 : expression (bv 16)) <- eval (extract v_5 32 48);
      v_15 <- eval (sub (concat (expression.bv_nat 2 0) v_13) (concat (expression.bv_nat 2 0) v_14));
      (v_16 : expression (bv 16)) <- eval (extract v_15 2 18);
      (v_17 : expression (bv 16)) <- eval (extract v_2 48 64);
      (v_18 : expression (bv 16)) <- eval (extract v_5 48 64);
      v_19 <- eval (sub (concat (expression.bv_nat 2 0) v_17) (concat (expression.bv_nat 2 0) v_18));
      (v_20 : expression (bv 16)) <- eval (extract v_19 2 18);
      (v_21 : expression (bv 16)) <- eval (extract v_2 64 80);
      (v_22 : expression (bv 16)) <- eval (extract v_5 64 80);
      v_23 <- eval (sub (concat (expression.bv_nat 2 0) v_21) (concat (expression.bv_nat 2 0) v_22));
      (v_24 : expression (bv 16)) <- eval (extract v_23 2 18);
      (v_25 : expression (bv 16)) <- eval (extract v_2 80 96);
      (v_26 : expression (bv 16)) <- eval (extract v_5 80 96);
      v_27 <- eval (sub (concat (expression.bv_nat 2 0) v_25) (concat (expression.bv_nat 2 0) v_26));
      (v_28 : expression (bv 16)) <- eval (extract v_27 2 18);
      (v_29 : expression (bv 16)) <- eval (extract v_2 96 112);
      (v_30 : expression (bv 16)) <- eval (extract v_5 96 112);
      v_31 <- eval (sub (concat (expression.bv_nat 2 0) v_29) (concat (expression.bv_nat 2 0) v_30));
      (v_32 : expression (bv 16)) <- eval (extract v_31 2 18);
      (v_33 : expression (bv 16)) <- eval (extract v_2 112 128);
      (v_34 : expression (bv 16)) <- eval (extract v_5 112 128);
      v_35 <- eval (sub (concat (expression.bv_nat 2 0) v_33) (concat (expression.bv_nat 2 0) v_34));
      (v_36 : expression (bv 16)) <- eval (extract v_35 2 18);
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_7 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_7 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) v_8)) (concat (mux (sgt v_11 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_11 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) v_12)) (concat (mux (sgt v_15 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) v_16)) (concat (mux (sgt v_19 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_19 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) v_20)) (concat (mux (sgt v_23 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_23 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) v_24)) (concat (mux (sgt v_27 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_27 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) v_28)) (concat (mux (sgt v_31 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_31 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) v_32)) (mux (sgt v_35 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_35 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) v_36)))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      v_4 <- getRegister (lhs.of_reg xmm_0);
      (v_5 : expression (bv 16)) <- eval (extract v_4 0 16);
      v_6 <- eval (sub (concat (expression.bv_nat 2 0) v_3) (concat (expression.bv_nat 2 0) v_5));
      (v_7 : expression (bv 16)) <- eval (extract v_6 2 18);
      (v_8 : expression (bv 16)) <- eval (extract v_2 16 32);
      (v_9 : expression (bv 16)) <- eval (extract v_4 16 32);
      v_10 <- eval (sub (concat (expression.bv_nat 2 0) v_8) (concat (expression.bv_nat 2 0) v_9));
      (v_11 : expression (bv 16)) <- eval (extract v_10 2 18);
      (v_12 : expression (bv 16)) <- eval (extract v_2 32 48);
      (v_13 : expression (bv 16)) <- eval (extract v_4 32 48);
      v_14 <- eval (sub (concat (expression.bv_nat 2 0) v_12) (concat (expression.bv_nat 2 0) v_13));
      (v_15 : expression (bv 16)) <- eval (extract v_14 2 18);
      (v_16 : expression (bv 16)) <- eval (extract v_2 48 64);
      (v_17 : expression (bv 16)) <- eval (extract v_4 48 64);
      v_18 <- eval (sub (concat (expression.bv_nat 2 0) v_16) (concat (expression.bv_nat 2 0) v_17));
      (v_19 : expression (bv 16)) <- eval (extract v_18 2 18);
      (v_20 : expression (bv 16)) <- eval (extract v_2 64 80);
      (v_21 : expression (bv 16)) <- eval (extract v_4 64 80);
      v_22 <- eval (sub (concat (expression.bv_nat 2 0) v_20) (concat (expression.bv_nat 2 0) v_21));
      (v_23 : expression (bv 16)) <- eval (extract v_22 2 18);
      (v_24 : expression (bv 16)) <- eval (extract v_2 80 96);
      (v_25 : expression (bv 16)) <- eval (extract v_4 80 96);
      v_26 <- eval (sub (concat (expression.bv_nat 2 0) v_24) (concat (expression.bv_nat 2 0) v_25));
      (v_27 : expression (bv 16)) <- eval (extract v_26 2 18);
      (v_28 : expression (bv 16)) <- eval (extract v_2 96 112);
      (v_29 : expression (bv 16)) <- eval (extract v_4 96 112);
      v_30 <- eval (sub (concat (expression.bv_nat 2 0) v_28) (concat (expression.bv_nat 2 0) v_29));
      (v_31 : expression (bv 16)) <- eval (extract v_30 2 18);
      (v_32 : expression (bv 16)) <- eval (extract v_2 112 128);
      (v_33 : expression (bv 16)) <- eval (extract v_4 112 128);
      v_34 <- eval (sub (concat (expression.bv_nat 2 0) v_32) (concat (expression.bv_nat 2 0) v_33));
      (v_35 : expression (bv 16)) <- eval (extract v_34 2 18);
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_6 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_6 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) v_7)) (concat (mux (sgt v_10 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_10 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) v_11)) (concat (mux (sgt v_14 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_14 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) v_15)) (concat (mux (sgt v_18 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_18 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) v_19)) (concat (mux (sgt v_22 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_22 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) v_23)) (concat (mux (sgt v_26 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_26 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) v_27)) (concat (mux (sgt v_30 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_30 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) v_31)) (mux (sgt v_34 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_34 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) v_35)))))))));
      pure ()
    pat_end
