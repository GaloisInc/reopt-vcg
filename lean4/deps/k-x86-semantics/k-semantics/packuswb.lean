def packuswb : instruction :=
  definst "packuswb" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      (v_5 : expression (bv 8)) <- eval (extract v_3 8 16);
      (v_6 : expression (bv 16)) <- eval (extract v_3 16 32);
      (v_7 : expression (bv 8)) <- eval (extract v_3 24 32);
      (v_8 : expression (bv 16)) <- eval (extract v_3 32 48);
      (v_9 : expression (bv 8)) <- eval (extract v_3 40 48);
      (v_10 : expression (bv 16)) <- eval (extract v_3 48 64);
      (v_11 : expression (bv 8)) <- eval (extract v_3 56 64);
      (v_12 : expression (bv 16)) <- eval (extract v_3 64 80);
      (v_13 : expression (bv 8)) <- eval (extract v_3 72 80);
      (v_14 : expression (bv 16)) <- eval (extract v_3 80 96);
      (v_15 : expression (bv 8)) <- eval (extract v_3 88 96);
      (v_16 : expression (bv 16)) <- eval (extract v_3 96 112);
      (v_17 : expression (bv 8)) <- eval (extract v_3 104 112);
      (v_18 : expression (bv 16)) <- eval (extract v_3 112 128);
      (v_19 : expression (bv 8)) <- eval (extract v_3 120 128);
      v_20 <- getRegister (lhs.of_reg xmm_1);
      (v_21 : expression (bv 16)) <- eval (extract v_20 0 16);
      (v_22 : expression (bv 8)) <- eval (extract v_20 8 16);
      (v_23 : expression (bv 16)) <- eval (extract v_20 16 32);
      (v_24 : expression (bv 8)) <- eval (extract v_20 24 32);
      (v_25 : expression (bv 16)) <- eval (extract v_20 32 48);
      (v_26 : expression (bv 8)) <- eval (extract v_20 40 48);
      (v_27 : expression (bv 16)) <- eval (extract v_20 48 64);
      (v_28 : expression (bv 8)) <- eval (extract v_20 56 64);
      (v_29 : expression (bv 16)) <- eval (extract v_20 64 80);
      (v_30 : expression (bv 8)) <- eval (extract v_20 72 80);
      (v_31 : expression (bv 16)) <- eval (extract v_20 80 96);
      (v_32 : expression (bv 8)) <- eval (extract v_20 88 96);
      (v_33 : expression (bv 16)) <- eval (extract v_20 96 112);
      (v_34 : expression (bv 8)) <- eval (extract v_20 104 112);
      (v_35 : expression (bv 16)) <- eval (extract v_20 112 128);
      (v_36 : expression (bv 8)) <- eval (extract v_20 120 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_4 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_4 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_5)) (concat (mux (sgt v_6 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_6 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_7)) (concat (mux (sgt v_8 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_8 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_9)) (concat (mux (sgt v_10 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_10 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_11)) (concat (mux (sgt v_12 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_12 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_13)) (concat (mux (sgt v_14 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_14 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_15)) (concat (mux (sgt v_16 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_16 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_17)) (concat (mux (sgt v_18 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_18 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_19)) (concat (mux (sgt v_21 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_21 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_22)) (concat (mux (sgt v_23 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_23 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_24)) (concat (mux (sgt v_25 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_25 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_26)) (concat (mux (sgt v_27 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_27 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_28)) (concat (mux (sgt v_29 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_29 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_30)) (concat (mux (sgt v_31 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_31 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_32)) (concat (mux (sgt v_33 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_33 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_34)) (mux (sgt v_35 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_35 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_36)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      (v_4 : expression (bv 8)) <- eval (extract v_2 8 16);
      (v_5 : expression (bv 16)) <- eval (extract v_2 16 32);
      (v_6 : expression (bv 8)) <- eval (extract v_2 24 32);
      (v_7 : expression (bv 16)) <- eval (extract v_2 32 48);
      (v_8 : expression (bv 8)) <- eval (extract v_2 40 48);
      (v_9 : expression (bv 16)) <- eval (extract v_2 48 64);
      (v_10 : expression (bv 8)) <- eval (extract v_2 56 64);
      (v_11 : expression (bv 16)) <- eval (extract v_2 64 80);
      (v_12 : expression (bv 8)) <- eval (extract v_2 72 80);
      (v_13 : expression (bv 16)) <- eval (extract v_2 80 96);
      (v_14 : expression (bv 8)) <- eval (extract v_2 88 96);
      (v_15 : expression (bv 16)) <- eval (extract v_2 96 112);
      (v_16 : expression (bv 8)) <- eval (extract v_2 104 112);
      (v_17 : expression (bv 16)) <- eval (extract v_2 112 128);
      (v_18 : expression (bv 8)) <- eval (extract v_2 120 128);
      v_19 <- getRegister (lhs.of_reg xmm_1);
      (v_20 : expression (bv 16)) <- eval (extract v_19 0 16);
      (v_21 : expression (bv 8)) <- eval (extract v_19 8 16);
      (v_22 : expression (bv 16)) <- eval (extract v_19 16 32);
      (v_23 : expression (bv 8)) <- eval (extract v_19 24 32);
      (v_24 : expression (bv 16)) <- eval (extract v_19 32 48);
      (v_25 : expression (bv 8)) <- eval (extract v_19 40 48);
      (v_26 : expression (bv 16)) <- eval (extract v_19 48 64);
      (v_27 : expression (bv 8)) <- eval (extract v_19 56 64);
      (v_28 : expression (bv 16)) <- eval (extract v_19 64 80);
      (v_29 : expression (bv 8)) <- eval (extract v_19 72 80);
      (v_30 : expression (bv 16)) <- eval (extract v_19 80 96);
      (v_31 : expression (bv 8)) <- eval (extract v_19 88 96);
      (v_32 : expression (bv 16)) <- eval (extract v_19 96 112);
      (v_33 : expression (bv 8)) <- eval (extract v_19 104 112);
      (v_34 : expression (bv 16)) <- eval (extract v_19 112 128);
      (v_35 : expression (bv 8)) <- eval (extract v_19 120 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_3 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_3 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_4)) (concat (mux (sgt v_5 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_6)) (concat (mux (sgt v_7 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_7 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_8)) (concat (mux (sgt v_9 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_10)) (concat (mux (sgt v_11 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_11 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_12)) (concat (mux (sgt v_13 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_13 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_14)) (concat (mux (sgt v_15 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_15 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_16)) (concat (mux (sgt v_17 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_17 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_18)) (concat (mux (sgt v_20 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_20 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_21)) (concat (mux (sgt v_22 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_22 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_23)) (concat (mux (sgt v_24 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_24 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_25)) (concat (mux (sgt v_26 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_26 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_27)) (concat (mux (sgt v_28 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_28 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_29)) (concat (mux (sgt v_30 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_30 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_31)) (concat (mux (sgt v_32 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_32 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_33)) (mux (sgt v_34 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_34 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) v_35)))))))))))))))));
      pure ()
    pat_end
