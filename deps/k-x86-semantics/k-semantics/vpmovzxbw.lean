def vpmovzxbw : instruction :=
  definst "vpmovzxbw" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 8;
      let (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      let (v_5 : expression (bv 8)) <- eval (extract v_3 8 16);
      let (v_6 : expression (bv 8)) <- eval (extract v_3 16 24);
      let (v_7 : expression (bv 8)) <- eval (extract v_3 24 32);
      let (v_8 : expression (bv 8)) <- eval (extract v_3 32 40);
      let (v_9 : expression (bv 8)) <- eval (extract v_3 40 48);
      let (v_10 : expression (bv 8)) <- eval (extract v_3 48 56);
      let (v_11 : expression (bv 8)) <- eval (extract v_3 56 64);
      let v_12 <- eval (concat (expression.bv_nat 8 0) v_11);
      let v_13 <- eval (concat v_10 v_12);
      let v_14 <- eval (concat (expression.bv_nat 8 0) v_13);
      let v_15 <- eval (concat v_9 v_14);
      let v_16 <- eval (concat (expression.bv_nat 8 0) v_15);
      let v_17 <- eval (concat v_8 v_16);
      let v_18 <- eval (concat (expression.bv_nat 8 0) v_17);
      let v_19 <- eval (concat v_7 v_18);
      let v_20 <- eval (concat (expression.bv_nat 8 0) v_19);
      let v_21 <- eval (concat v_6 v_20);
      let v_22 <- eval (concat (expression.bv_nat 8 0) v_21);
      let v_23 <- eval (concat v_5 v_22);
      let v_24 <- eval (concat (expression.bv_nat 8 0) v_23);
      let v_25 <- eval (concat v_4 v_24);
      let v_26 <- eval (concat (expression.bv_nat 8 0) v_25);
      setRegister (lhs.of_reg xmm_1) v_26;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      let (v_5 : expression (bv 8)) <- eval (extract v_3 8 16);
      let (v_6 : expression (bv 8)) <- eval (extract v_3 16 24);
      let (v_7 : expression (bv 8)) <- eval (extract v_3 24 32);
      let (v_8 : expression (bv 8)) <- eval (extract v_3 32 40);
      let (v_9 : expression (bv 8)) <- eval (extract v_3 40 48);
      let (v_10 : expression (bv 8)) <- eval (extract v_3 48 56);
      let (v_11 : expression (bv 8)) <- eval (extract v_3 56 64);
      let (v_12 : expression (bv 8)) <- eval (extract v_3 64 72);
      let (v_13 : expression (bv 8)) <- eval (extract v_3 72 80);
      let (v_14 : expression (bv 8)) <- eval (extract v_3 80 88);
      let (v_15 : expression (bv 8)) <- eval (extract v_3 88 96);
      let (v_16 : expression (bv 8)) <- eval (extract v_3 96 104);
      let (v_17 : expression (bv 8)) <- eval (extract v_3 104 112);
      let (v_18 : expression (bv 8)) <- eval (extract v_3 112 120);
      let (v_19 : expression (bv 8)) <- eval (extract v_3 120 128);
      let v_20 <- eval (concat (expression.bv_nat 8 0) v_19);
      let v_21 <- eval (concat v_18 v_20);
      let v_22 <- eval (concat (expression.bv_nat 8 0) v_21);
      let v_23 <- eval (concat v_17 v_22);
      let v_24 <- eval (concat (expression.bv_nat 8 0) v_23);
      let v_25 <- eval (concat v_16 v_24);
      let v_26 <- eval (concat (expression.bv_nat 8 0) v_25);
      let v_27 <- eval (concat v_15 v_26);
      let v_28 <- eval (concat (expression.bv_nat 8 0) v_27);
      let v_29 <- eval (concat v_14 v_28);
      let v_30 <- eval (concat (expression.bv_nat 8 0) v_29);
      let v_31 <- eval (concat v_13 v_30);
      let v_32 <- eval (concat (expression.bv_nat 8 0) v_31);
      let v_33 <- eval (concat v_12 v_32);
      let v_34 <- eval (concat (expression.bv_nat 8 0) v_33);
      let v_35 <- eval (concat v_11 v_34);
      let v_36 <- eval (concat (expression.bv_nat 8 0) v_35);
      let v_37 <- eval (concat v_10 v_36);
      let v_38 <- eval (concat (expression.bv_nat 8 0) v_37);
      let v_39 <- eval (concat v_9 v_38);
      let v_40 <- eval (concat (expression.bv_nat 8 0) v_39);
      let v_41 <- eval (concat v_8 v_40);
      let v_42 <- eval (concat (expression.bv_nat 8 0) v_41);
      let v_43 <- eval (concat v_7 v_42);
      let v_44 <- eval (concat (expression.bv_nat 8 0) v_43);
      let v_45 <- eval (concat v_6 v_44);
      let v_46 <- eval (concat (expression.bv_nat 8 0) v_45);
      let v_47 <- eval (concat v_5 v_46);
      let v_48 <- eval (concat (expression.bv_nat 8 0) v_47);
      let v_49 <- eval (concat v_4 v_48);
      let v_50 <- eval (concat (expression.bv_nat 8 0) v_49);
      setRegister (lhs.of_reg ymm_1) v_50;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 8)) <- eval (extract v_2 64 72);
      let (v_4 : expression (bv 8)) <- eval (extract v_2 72 80);
      let (v_5 : expression (bv 8)) <- eval (extract v_2 80 88);
      let (v_6 : expression (bv 8)) <- eval (extract v_2 88 96);
      let (v_7 : expression (bv 8)) <- eval (extract v_2 96 104);
      let (v_8 : expression (bv 8)) <- eval (extract v_2 104 112);
      let (v_9 : expression (bv 8)) <- eval (extract v_2 112 120);
      let (v_10 : expression (bv 8)) <- eval (extract v_2 120 128);
      let v_11 <- eval (concat (expression.bv_nat 8 0) v_10);
      let v_12 <- eval (concat v_9 v_11);
      let v_13 <- eval (concat (expression.bv_nat 8 0) v_12);
      let v_14 <- eval (concat v_8 v_13);
      let v_15 <- eval (concat (expression.bv_nat 8 0) v_14);
      let v_16 <- eval (concat v_7 v_15);
      let v_17 <- eval (concat (expression.bv_nat 8 0) v_16);
      let v_18 <- eval (concat v_6 v_17);
      let v_19 <- eval (concat (expression.bv_nat 8 0) v_18);
      let v_20 <- eval (concat v_5 v_19);
      let v_21 <- eval (concat (expression.bv_nat 8 0) v_20);
      let v_22 <- eval (concat v_4 v_21);
      let v_23 <- eval (concat (expression.bv_nat 8 0) v_22);
      let v_24 <- eval (concat v_3 v_23);
      let v_25 <- eval (concat (expression.bv_nat 8 0) v_24);
      setRegister (lhs.of_reg xmm_1) v_25;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 8)) <- eval (extract v_2 0 8);
      let (v_4 : expression (bv 8)) <- eval (extract v_2 8 16);
      let (v_5 : expression (bv 8)) <- eval (extract v_2 16 24);
      let (v_6 : expression (bv 8)) <- eval (extract v_2 24 32);
      let (v_7 : expression (bv 8)) <- eval (extract v_2 32 40);
      let (v_8 : expression (bv 8)) <- eval (extract v_2 40 48);
      let (v_9 : expression (bv 8)) <- eval (extract v_2 48 56);
      let (v_10 : expression (bv 8)) <- eval (extract v_2 56 64);
      let (v_11 : expression (bv 8)) <- eval (extract v_2 64 72);
      let (v_12 : expression (bv 8)) <- eval (extract v_2 72 80);
      let (v_13 : expression (bv 8)) <- eval (extract v_2 80 88);
      let (v_14 : expression (bv 8)) <- eval (extract v_2 88 96);
      let (v_15 : expression (bv 8)) <- eval (extract v_2 96 104);
      let (v_16 : expression (bv 8)) <- eval (extract v_2 104 112);
      let (v_17 : expression (bv 8)) <- eval (extract v_2 112 120);
      let (v_18 : expression (bv 8)) <- eval (extract v_2 120 128);
      let v_19 <- eval (concat (expression.bv_nat 8 0) v_18);
      let v_20 <- eval (concat v_17 v_19);
      let v_21 <- eval (concat (expression.bv_nat 8 0) v_20);
      let v_22 <- eval (concat v_16 v_21);
      let v_23 <- eval (concat (expression.bv_nat 8 0) v_22);
      let v_24 <- eval (concat v_15 v_23);
      let v_25 <- eval (concat (expression.bv_nat 8 0) v_24);
      let v_26 <- eval (concat v_14 v_25);
      let v_27 <- eval (concat (expression.bv_nat 8 0) v_26);
      let v_28 <- eval (concat v_13 v_27);
      let v_29 <- eval (concat (expression.bv_nat 8 0) v_28);
      let v_30 <- eval (concat v_12 v_29);
      let v_31 <- eval (concat (expression.bv_nat 8 0) v_30);
      let v_32 <- eval (concat v_11 v_31);
      let v_33 <- eval (concat (expression.bv_nat 8 0) v_32);
      let v_34 <- eval (concat v_10 v_33);
      let v_35 <- eval (concat (expression.bv_nat 8 0) v_34);
      let v_36 <- eval (concat v_9 v_35);
      let v_37 <- eval (concat (expression.bv_nat 8 0) v_36);
      let v_38 <- eval (concat v_8 v_37);
      let v_39 <- eval (concat (expression.bv_nat 8 0) v_38);
      let v_40 <- eval (concat v_7 v_39);
      let v_41 <- eval (concat (expression.bv_nat 8 0) v_40);
      let v_42 <- eval (concat v_6 v_41);
      let v_43 <- eval (concat (expression.bv_nat 8 0) v_42);
      let v_44 <- eval (concat v_5 v_43);
      let v_45 <- eval (concat (expression.bv_nat 8 0) v_44);
      let v_46 <- eval (concat v_4 v_45);
      let v_47 <- eval (concat (expression.bv_nat 8 0) v_46);
      let v_48 <- eval (concat v_3 v_47);
      let v_49 <- eval (concat (expression.bv_nat 8 0) v_48);
      setRegister (lhs.of_reg ymm_1) v_49;
      pure ()
     action
