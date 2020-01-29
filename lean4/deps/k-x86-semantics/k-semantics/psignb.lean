def psignb : instruction :=
  definst "psignb" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      (v_6 : expression (bv 8)) <- eval (extract v_5 0 8);
      (v_7 : expression (bv 8)) <- eval (extract v_3 8 16);
      (v_8 : expression (bv 8)) <- eval (extract v_5 8 16);
      (v_9 : expression (bv 8)) <- eval (extract v_3 16 24);
      (v_10 : expression (bv 8)) <- eval (extract v_5 16 24);
      (v_11 : expression (bv 8)) <- eval (extract v_3 24 32);
      (v_12 : expression (bv 8)) <- eval (extract v_5 24 32);
      (v_13 : expression (bv 8)) <- eval (extract v_3 32 40);
      (v_14 : expression (bv 8)) <- eval (extract v_5 32 40);
      (v_15 : expression (bv 8)) <- eval (extract v_3 40 48);
      (v_16 : expression (bv 8)) <- eval (extract v_5 40 48);
      (v_17 : expression (bv 8)) <- eval (extract v_3 48 56);
      (v_18 : expression (bv 8)) <- eval (extract v_5 48 56);
      (v_19 : expression (bv 8)) <- eval (extract v_3 56 64);
      (v_20 : expression (bv 8)) <- eval (extract v_5 56 64);
      (v_21 : expression (bv 8)) <- eval (extract v_3 64 72);
      (v_22 : expression (bv 8)) <- eval (extract v_5 64 72);
      (v_23 : expression (bv 8)) <- eval (extract v_3 72 80);
      (v_24 : expression (bv 8)) <- eval (extract v_5 72 80);
      (v_25 : expression (bv 8)) <- eval (extract v_3 80 88);
      (v_26 : expression (bv 8)) <- eval (extract v_5 80 88);
      (v_27 : expression (bv 8)) <- eval (extract v_3 88 96);
      (v_28 : expression (bv 8)) <- eval (extract v_5 88 96);
      (v_29 : expression (bv 8)) <- eval (extract v_3 96 104);
      (v_30 : expression (bv 8)) <- eval (extract v_5 96 104);
      (v_31 : expression (bv 8)) <- eval (extract v_3 104 112);
      (v_32 : expression (bv 8)) <- eval (extract v_5 104 112);
      (v_33 : expression (bv 8)) <- eval (extract v_3 112 120);
      (v_34 : expression (bv 8)) <- eval (extract v_5 112 120);
      (v_35 : expression (bv 8)) <- eval (extract v_3 120 128);
      (v_36 : expression (bv 8)) <- eval (extract v_5 120 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_4 (expression.bv_nat 8 0)) v_6 (mux (eq v_4 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_6 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7 (expression.bv_nat 8 0)) v_8 (mux (eq v_7 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_8 (expression.bv_nat 8 255))))) (concat (mux (sgt v_9 (expression.bv_nat 8 0)) v_10 (mux (eq v_9 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_10 (expression.bv_nat 8 255))))) (concat (mux (sgt v_11 (expression.bv_nat 8 0)) v_12 (mux (eq v_11 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_12 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13 (expression.bv_nat 8 0)) v_14 (mux (eq v_13 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14 (expression.bv_nat 8 255))))) (concat (mux (sgt v_15 (expression.bv_nat 8 0)) v_16 (mux (eq v_15 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_16 (expression.bv_nat 8 255))))) (concat (mux (sgt v_17 (expression.bv_nat 8 0)) v_18 (mux (eq v_17 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_18 (expression.bv_nat 8 255))))) (concat (mux (sgt v_19 (expression.bv_nat 8 0)) v_20 (mux (eq v_19 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_20 (expression.bv_nat 8 255))))) (concat (mux (sgt v_21 (expression.bv_nat 8 0)) v_22 (mux (eq v_21 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_22 (expression.bv_nat 8 255))))) (concat (mux (sgt v_23 (expression.bv_nat 8 0)) v_24 (mux (eq v_23 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_24 (expression.bv_nat 8 255))))) (concat (mux (sgt v_25 (expression.bv_nat 8 0)) v_26 (mux (eq v_25 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_26 (expression.bv_nat 8 255))))) (concat (mux (sgt v_27 (expression.bv_nat 8 0)) v_28 (mux (eq v_27 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_28 (expression.bv_nat 8 255))))) (concat (mux (sgt v_29 (expression.bv_nat 8 0)) v_30 (mux (eq v_29 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_30 (expression.bv_nat 8 255))))) (concat (mux (sgt v_31 (expression.bv_nat 8 0)) v_32 (mux (eq v_31 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_32 (expression.bv_nat 8 255))))) (concat (mux (sgt v_33 (expression.bv_nat 8 0)) v_34 (mux (eq v_33 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_34 (expression.bv_nat 8 255))))) (mux (sgt v_35 (expression.bv_nat 8 0)) v_36 (mux (eq v_35 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_36 (expression.bv_nat 8 255))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 8)) <- eval (extract v_2 0 8);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      (v_5 : expression (bv 8)) <- eval (extract v_4 0 8);
      (v_6 : expression (bv 8)) <- eval (extract v_2 8 16);
      (v_7 : expression (bv 8)) <- eval (extract v_4 8 16);
      (v_8 : expression (bv 8)) <- eval (extract v_2 16 24);
      (v_9 : expression (bv 8)) <- eval (extract v_4 16 24);
      (v_10 : expression (bv 8)) <- eval (extract v_2 24 32);
      (v_11 : expression (bv 8)) <- eval (extract v_4 24 32);
      (v_12 : expression (bv 8)) <- eval (extract v_2 32 40);
      (v_13 : expression (bv 8)) <- eval (extract v_4 32 40);
      (v_14 : expression (bv 8)) <- eval (extract v_2 40 48);
      (v_15 : expression (bv 8)) <- eval (extract v_4 40 48);
      (v_16 : expression (bv 8)) <- eval (extract v_2 48 56);
      (v_17 : expression (bv 8)) <- eval (extract v_4 48 56);
      (v_18 : expression (bv 8)) <- eval (extract v_2 56 64);
      (v_19 : expression (bv 8)) <- eval (extract v_4 56 64);
      (v_20 : expression (bv 8)) <- eval (extract v_2 64 72);
      (v_21 : expression (bv 8)) <- eval (extract v_4 64 72);
      (v_22 : expression (bv 8)) <- eval (extract v_2 72 80);
      (v_23 : expression (bv 8)) <- eval (extract v_4 72 80);
      (v_24 : expression (bv 8)) <- eval (extract v_2 80 88);
      (v_25 : expression (bv 8)) <- eval (extract v_4 80 88);
      (v_26 : expression (bv 8)) <- eval (extract v_2 88 96);
      (v_27 : expression (bv 8)) <- eval (extract v_4 88 96);
      (v_28 : expression (bv 8)) <- eval (extract v_2 96 104);
      (v_29 : expression (bv 8)) <- eval (extract v_4 96 104);
      (v_30 : expression (bv 8)) <- eval (extract v_2 104 112);
      (v_31 : expression (bv 8)) <- eval (extract v_4 104 112);
      (v_32 : expression (bv 8)) <- eval (extract v_2 112 120);
      (v_33 : expression (bv 8)) <- eval (extract v_4 112 120);
      (v_34 : expression (bv 8)) <- eval (extract v_2 120 128);
      (v_35 : expression (bv 8)) <- eval (extract v_4 120 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_3 (expression.bv_nat 8 0)) v_5 (mux (eq v_3 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_5 (expression.bv_nat 8 255))))) (concat (mux (sgt v_6 (expression.bv_nat 8 0)) v_7 (mux (eq v_6 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7 (expression.bv_nat 8 255))))) (concat (mux (sgt v_8 (expression.bv_nat 8 0)) v_9 (mux (eq v_8 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_9 (expression.bv_nat 8 255))))) (concat (mux (sgt v_10 (expression.bv_nat 8 0)) v_11 (mux (eq v_10 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_11 (expression.bv_nat 8 255))))) (concat (mux (sgt v_12 (expression.bv_nat 8 0)) v_13 (mux (eq v_12 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14 (expression.bv_nat 8 0)) v_15 (mux (eq v_14 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_15 (expression.bv_nat 8 255))))) (concat (mux (sgt v_16 (expression.bv_nat 8 0)) v_17 (mux (eq v_16 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_17 (expression.bv_nat 8 255))))) (concat (mux (sgt v_18 (expression.bv_nat 8 0)) v_19 (mux (eq v_18 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_19 (expression.bv_nat 8 255))))) (concat (mux (sgt v_20 (expression.bv_nat 8 0)) v_21 (mux (eq v_20 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_21 (expression.bv_nat 8 255))))) (concat (mux (sgt v_22 (expression.bv_nat 8 0)) v_23 (mux (eq v_22 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_23 (expression.bv_nat 8 255))))) (concat (mux (sgt v_24 (expression.bv_nat 8 0)) v_25 (mux (eq v_24 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_25 (expression.bv_nat 8 255))))) (concat (mux (sgt v_26 (expression.bv_nat 8 0)) v_27 (mux (eq v_26 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_27 (expression.bv_nat 8 255))))) (concat (mux (sgt v_28 (expression.bv_nat 8 0)) v_29 (mux (eq v_28 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_29 (expression.bv_nat 8 255))))) (concat (mux (sgt v_30 (expression.bv_nat 8 0)) v_31 (mux (eq v_30 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_31 (expression.bv_nat 8 255))))) (concat (mux (sgt v_32 (expression.bv_nat 8 0)) v_33 (mux (eq v_32 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_33 (expression.bv_nat 8 255))))) (mux (sgt v_34 (expression.bv_nat 8 0)) v_35 (mux (eq v_34 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_35 (expression.bv_nat 8 255))))))))))))))))))));
      pure ()
    pat_end
