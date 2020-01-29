def paddusw : instruction :=
  definst "paddusw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 16;
      (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      v_7 <- eval (add (concat (expression.bv_nat 1 0) v_3) (concat (expression.bv_nat 1 0) v_6));
      (v_8 : expression (bv 16)) <- eval (extract v_7 1 17);
      (v_9 : expression (bv 16)) <- eval (extract v_2 16 32);
      (v_10 : expression (bv 16)) <- eval (extract v_5 16 32);
      v_11 <- eval (add (concat (expression.bv_nat 1 0) v_9) (concat (expression.bv_nat 1 0) v_10));
      (v_12 : expression (bv 16)) <- eval (extract v_11 1 17);
      (v_13 : expression (bv 16)) <- eval (extract v_2 32 48);
      (v_14 : expression (bv 16)) <- eval (extract v_5 32 48);
      v_15 <- eval (add (concat (expression.bv_nat 1 0) v_13) (concat (expression.bv_nat 1 0) v_14));
      (v_16 : expression (bv 16)) <- eval (extract v_15 1 17);
      (v_17 : expression (bv 16)) <- eval (extract v_2 48 64);
      (v_18 : expression (bv 16)) <- eval (extract v_5 48 64);
      v_19 <- eval (add (concat (expression.bv_nat 1 0) v_17) (concat (expression.bv_nat 1 0) v_18));
      (v_20 : expression (bv 16)) <- eval (extract v_19 1 17);
      (v_21 : expression (bv 16)) <- eval (extract v_2 64 80);
      (v_22 : expression (bv 16)) <- eval (extract v_5 64 80);
      v_23 <- eval (add (concat (expression.bv_nat 1 0) v_21) (concat (expression.bv_nat 1 0) v_22));
      (v_24 : expression (bv 16)) <- eval (extract v_23 1 17);
      (v_25 : expression (bv 16)) <- eval (extract v_2 80 96);
      (v_26 : expression (bv 16)) <- eval (extract v_5 80 96);
      v_27 <- eval (add (concat (expression.bv_nat 1 0) v_25) (concat (expression.bv_nat 1 0) v_26));
      (v_28 : expression (bv 16)) <- eval (extract v_27 1 17);
      (v_29 : expression (bv 16)) <- eval (extract v_2 96 112);
      (v_30 : expression (bv 16)) <- eval (extract v_5 96 112);
      v_31 <- eval (add (concat (expression.bv_nat 1 0) v_29) (concat (expression.bv_nat 1 0) v_30));
      (v_32 : expression (bv 16)) <- eval (extract v_31 1 17);
      (v_33 : expression (bv 16)) <- eval (extract v_2 112 128);
      (v_34 : expression (bv 16)) <- eval (extract v_5 112 128);
      v_35 <- eval (add (concat (expression.bv_nat 1 0) v_33) (concat (expression.bv_nat 1 0) v_34));
      (v_36 : expression (bv 16)) <- eval (extract v_35 1 17);
      setRegister (lhs.of_reg xmm_1) (concat (mux (isBitSet v_7 0) (expression.bv_nat 16 65535) v_8) (concat (mux (isBitSet v_11 0) (expression.bv_nat 16 65535) v_12) (concat (mux (isBitSet v_15 0) (expression.bv_nat 16 65535) v_16) (concat (mux (isBitSet v_19 0) (expression.bv_nat 16 65535) v_20) (concat (mux (isBitSet v_23 0) (expression.bv_nat 16 65535) v_24) (concat (mux (isBitSet v_27 0) (expression.bv_nat 16 65535) v_28) (concat (mux (isBitSet v_31 0) (expression.bv_nat 16 65535) v_32) (mux (isBitSet v_35 0) (expression.bv_nat 16 65535) v_36))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      v_4 <- getRegister (lhs.of_reg xmm_0);
      (v_5 : expression (bv 16)) <- eval (extract v_4 0 16);
      v_6 <- eval (add (concat (expression.bv_nat 1 0) v_3) (concat (expression.bv_nat 1 0) v_5));
      (v_7 : expression (bv 16)) <- eval (extract v_6 1 17);
      (v_8 : expression (bv 16)) <- eval (extract v_2 16 32);
      (v_9 : expression (bv 16)) <- eval (extract v_4 16 32);
      v_10 <- eval (add (concat (expression.bv_nat 1 0) v_8) (concat (expression.bv_nat 1 0) v_9));
      (v_11 : expression (bv 16)) <- eval (extract v_10 1 17);
      (v_12 : expression (bv 16)) <- eval (extract v_2 32 48);
      (v_13 : expression (bv 16)) <- eval (extract v_4 32 48);
      v_14 <- eval (add (concat (expression.bv_nat 1 0) v_12) (concat (expression.bv_nat 1 0) v_13));
      (v_15 : expression (bv 16)) <- eval (extract v_14 1 17);
      (v_16 : expression (bv 16)) <- eval (extract v_2 48 64);
      (v_17 : expression (bv 16)) <- eval (extract v_4 48 64);
      v_18 <- eval (add (concat (expression.bv_nat 1 0) v_16) (concat (expression.bv_nat 1 0) v_17));
      (v_19 : expression (bv 16)) <- eval (extract v_18 1 17);
      (v_20 : expression (bv 16)) <- eval (extract v_2 64 80);
      (v_21 : expression (bv 16)) <- eval (extract v_4 64 80);
      v_22 <- eval (add (concat (expression.bv_nat 1 0) v_20) (concat (expression.bv_nat 1 0) v_21));
      (v_23 : expression (bv 16)) <- eval (extract v_22 1 17);
      (v_24 : expression (bv 16)) <- eval (extract v_2 80 96);
      (v_25 : expression (bv 16)) <- eval (extract v_4 80 96);
      v_26 <- eval (add (concat (expression.bv_nat 1 0) v_24) (concat (expression.bv_nat 1 0) v_25));
      (v_27 : expression (bv 16)) <- eval (extract v_26 1 17);
      (v_28 : expression (bv 16)) <- eval (extract v_2 96 112);
      (v_29 : expression (bv 16)) <- eval (extract v_4 96 112);
      v_30 <- eval (add (concat (expression.bv_nat 1 0) v_28) (concat (expression.bv_nat 1 0) v_29));
      (v_31 : expression (bv 16)) <- eval (extract v_30 1 17);
      (v_32 : expression (bv 16)) <- eval (extract v_2 112 128);
      (v_33 : expression (bv 16)) <- eval (extract v_4 112 128);
      v_34 <- eval (add (concat (expression.bv_nat 1 0) v_32) (concat (expression.bv_nat 1 0) v_33));
      (v_35 : expression (bv 16)) <- eval (extract v_34 1 17);
      setRegister (lhs.of_reg xmm_1) (concat (mux (isBitSet v_6 0) (expression.bv_nat 16 65535) v_7) (concat (mux (isBitSet v_10 0) (expression.bv_nat 16 65535) v_11) (concat (mux (isBitSet v_14 0) (expression.bv_nat 16 65535) v_15) (concat (mux (isBitSet v_18 0) (expression.bv_nat 16 65535) v_19) (concat (mux (isBitSet v_22 0) (expression.bv_nat 16 65535) v_23) (concat (mux (isBitSet v_26 0) (expression.bv_nat 16 65535) v_27) (concat (mux (isBitSet v_30 0) (expression.bv_nat 16 65535) v_31) (mux (isBitSet v_34 0) (expression.bv_nat 16 65535) v_35))))))));
      pure ()
    pat_end
