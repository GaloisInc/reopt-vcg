def psadbw : instruction :=
  definst "psadbw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- eval (extract v_2 0 8);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 16;
      v_6 <- eval (extract v_5 0 8);
      v_7 <- eval (extract v_2 8 16);
      v_8 <- eval (extract v_5 8 16);
      v_9 <- eval (extract v_2 16 24);
      v_10 <- eval (extract v_5 16 24);
      v_11 <- eval (extract v_2 24 32);
      v_12 <- eval (extract v_5 24 32);
      v_13 <- eval (extract v_2 32 40);
      v_14 <- eval (extract v_5 32 40);
      v_15 <- eval (extract v_2 40 48);
      v_16 <- eval (extract v_5 40 48);
      v_17 <- eval (extract v_2 48 56);
      v_18 <- eval (extract v_5 48 56);
      v_19 <- eval (extract v_2 56 64);
      v_20 <- eval (extract v_5 56 64);
      v_21 <- eval (extract v_2 64 72);
      v_22 <- eval (extract v_5 64 72);
      v_23 <- eval (extract v_2 72 80);
      v_24 <- eval (extract v_5 72 80);
      v_25 <- eval (extract v_2 80 88);
      v_26 <- eval (extract v_5 80 88);
      v_27 <- eval (extract v_2 88 96);
      v_28 <- eval (extract v_5 88 96);
      v_29 <- eval (extract v_2 96 104);
      v_30 <- eval (extract v_5 96 104);
      v_31 <- eval (extract v_2 104 112);
      v_32 <- eval (extract v_5 104 112);
      v_33 <- eval (extract v_2 112 120);
      v_34 <- eval (extract v_5 112 120);
      v_35 <- eval (extract v_2 120 128);
      v_36 <- eval (extract v_5 120 128);
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 48 0) (concat (add (concat (expression.bv_nat 8 0) (mux (ugt v_3 v_6) (sub v_3 v_6) (sub v_6 v_3))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_7 v_8) (sub v_7 v_8) (sub v_8 v_7))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_9 v_10) (sub v_9 v_10) (sub v_10 v_9))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_11 v_12) (sub v_11 v_12) (sub v_12 v_11))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13 v_14) (sub v_13 v_14) (sub v_14 v_13))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_15 v_16) (sub v_15 v_16) (sub v_16 v_15))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_17 v_18) (sub v_17 v_18) (sub v_18 v_17))) (concat (expression.bv_nat 8 0) (mux (ugt v_19 v_20) (sub v_19 v_20) (sub v_20 v_19)))))))))) (concat (expression.bv_nat 48 0) (add (concat (expression.bv_nat 8 0) (mux (ugt v_21 v_22) (sub v_21 v_22) (sub v_22 v_21))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_23 v_24) (sub v_23 v_24) (sub v_24 v_23))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_25 v_26) (sub v_25 v_26) (sub v_26 v_25))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_27 v_28) (sub v_27 v_28) (sub v_28 v_27))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_29 v_30) (sub v_29 v_30) (sub v_30 v_29))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_31 v_32) (sub v_31 v_32) (sub v_32 v_31))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_33 v_34) (sub v_33 v_34) (sub v_34 v_33))) (concat (expression.bv_nat 8 0) (mux (ugt v_35 v_36) (sub v_35 v_36) (sub v_36 v_35)))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- eval (extract v_2 0 8);
      v_4 <- getRegister (lhs.of_reg xmm_0);
      v_5 <- eval (extract v_4 0 8);
      v_6 <- eval (extract v_2 8 16);
      v_7 <- eval (extract v_4 8 16);
      v_8 <- eval (extract v_2 16 24);
      v_9 <- eval (extract v_4 16 24);
      v_10 <- eval (extract v_2 24 32);
      v_11 <- eval (extract v_4 24 32);
      v_12 <- eval (extract v_2 32 40);
      v_13 <- eval (extract v_4 32 40);
      v_14 <- eval (extract v_2 40 48);
      v_15 <- eval (extract v_4 40 48);
      v_16 <- eval (extract v_2 48 56);
      v_17 <- eval (extract v_4 48 56);
      v_18 <- eval (extract v_2 56 64);
      v_19 <- eval (extract v_4 56 64);
      v_20 <- eval (extract v_2 64 72);
      v_21 <- eval (extract v_4 64 72);
      v_22 <- eval (extract v_2 72 80);
      v_23 <- eval (extract v_4 72 80);
      v_24 <- eval (extract v_2 80 88);
      v_25 <- eval (extract v_4 80 88);
      v_26 <- eval (extract v_2 88 96);
      v_27 <- eval (extract v_4 88 96);
      v_28 <- eval (extract v_2 96 104);
      v_29 <- eval (extract v_4 96 104);
      v_30 <- eval (extract v_2 104 112);
      v_31 <- eval (extract v_4 104 112);
      v_32 <- eval (extract v_2 112 120);
      v_33 <- eval (extract v_4 112 120);
      v_34 <- eval (extract v_2 120 128);
      v_35 <- eval (extract v_4 120 128);
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 48 0) (concat (add (concat (expression.bv_nat 8 0) (mux (ugt v_3 v_5) (sub v_3 v_5) (sub v_5 v_3))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6 v_7) (sub v_6 v_7) (sub v_7 v_6))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_8 v_9) (sub v_8 v_9) (sub v_9 v_8))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_10 v_11) (sub v_10 v_11) (sub v_11 v_10))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_12 v_13) (sub v_12 v_13) (sub v_13 v_12))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_14 v_15) (sub v_14 v_15) (sub v_15 v_14))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_16 v_17) (sub v_16 v_17) (sub v_17 v_16))) (concat (expression.bv_nat 8 0) (mux (ugt v_18 v_19) (sub v_18 v_19) (sub v_19 v_18)))))))))) (concat (expression.bv_nat 48 0) (add (concat (expression.bv_nat 8 0) (mux (ugt v_20 v_21) (sub v_20 v_21) (sub v_21 v_20))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_22 v_23) (sub v_22 v_23) (sub v_23 v_22))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_24 v_25) (sub v_24 v_25) (sub v_25 v_24))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_26 v_27) (sub v_26 v_27) (sub v_27 v_26))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_28 v_29) (sub v_28 v_29) (sub v_29 v_28))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_30 v_31) (sub v_30 v_31) (sub v_31 v_30))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_32 v_33) (sub v_32 v_33) (sub v_33 v_32))) (concat (expression.bv_nat 8 0) (mux (ugt v_34 v_35) (sub v_34 v_35) (sub v_35 v_34)))))))))))));
      pure ()
    pat_end
