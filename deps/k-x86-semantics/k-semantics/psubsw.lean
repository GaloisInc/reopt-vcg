def psubsw : instruction :=
  definst "psubsw" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 16;
      let (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      let v_7 <- eval (sub (sext v_3 18) (sext v_6 18));
      let (v_8 : expression (bv 16)) <- eval (extract v_7 2 18);
      let (v_9 : expression (bv 16)) <- eval (extract v_2 16 32);
      let (v_10 : expression (bv 16)) <- eval (extract v_5 16 32);
      let v_11 <- eval (sub (sext v_9 18) (sext v_10 18));
      let (v_12 : expression (bv 16)) <- eval (extract v_11 2 18);
      let (v_13 : expression (bv 16)) <- eval (extract v_2 32 48);
      let (v_14 : expression (bv 16)) <- eval (extract v_5 32 48);
      let v_15 <- eval (sub (sext v_13 18) (sext v_14 18));
      let (v_16 : expression (bv 16)) <- eval (extract v_15 2 18);
      let (v_17 : expression (bv 16)) <- eval (extract v_2 48 64);
      let (v_18 : expression (bv 16)) <- eval (extract v_5 48 64);
      let v_19 <- eval (sub (sext v_17 18) (sext v_18 18));
      let (v_20 : expression (bv 16)) <- eval (extract v_19 2 18);
      let (v_21 : expression (bv 16)) <- eval (extract v_2 64 80);
      let (v_22 : expression (bv 16)) <- eval (extract v_5 64 80);
      let v_23 <- eval (sub (sext v_21 18) (sext v_22 18));
      let (v_24 : expression (bv 16)) <- eval (extract v_23 2 18);
      let (v_25 : expression (bv 16)) <- eval (extract v_2 80 96);
      let (v_26 : expression (bv 16)) <- eval (extract v_5 80 96);
      let v_27 <- eval (sub (sext v_25 18) (sext v_26 18));
      let (v_28 : expression (bv 16)) <- eval (extract v_27 2 18);
      let (v_29 : expression (bv 16)) <- eval (extract v_2 96 112);
      let (v_30 : expression (bv 16)) <- eval (extract v_5 96 112);
      let v_31 <- eval (sub (sext v_29 18) (sext v_30 18));
      let (v_32 : expression (bv 16)) <- eval (extract v_31 2 18);
      let (v_33 : expression (bv 16)) <- eval (extract v_2 112 128);
      let (v_34 : expression (bv 16)) <- eval (extract v_5 112 128);
      let v_35 <- eval (sub (sext v_33 18) (sext v_34 18));
      let (v_36 : expression (bv 16)) <- eval (extract v_35 2 18);
      let v_37 <- eval (concat (mux (sgt v_31 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_31 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_32)) (mux (sgt v_35 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_35 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_36)));
      let v_38 <- eval (concat (mux (sgt v_27 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_27 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_28)) v_37);
      let v_39 <- eval (concat (mux (sgt v_23 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_23 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_24)) v_38);
      let v_40 <- eval (concat (mux (sgt v_19 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_19 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_20)) v_39);
      let v_41 <- eval (concat (mux (sgt v_15 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_15 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_16)) v_40);
      let v_42 <- eval (concat (mux (sgt v_11 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_12)) v_41);
      let v_43 <- eval (concat (mux (sgt v_7 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_7 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_8)) v_42);
      setRegister (lhs.of_reg xmm_1) v_43;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      let v_4 <- getRegister (lhs.of_reg xmm_0);
      let (v_5 : expression (bv 16)) <- eval (extract v_4 0 16);
      let v_6 <- eval (sub (sext v_3 18) (sext v_5 18));
      let (v_7 : expression (bv 16)) <- eval (extract v_6 2 18);
      let (v_8 : expression (bv 16)) <- eval (extract v_2 16 32);
      let (v_9 : expression (bv 16)) <- eval (extract v_4 16 32);
      let v_10 <- eval (sub (sext v_8 18) (sext v_9 18));
      let (v_11 : expression (bv 16)) <- eval (extract v_10 2 18);
      let (v_12 : expression (bv 16)) <- eval (extract v_2 32 48);
      let (v_13 : expression (bv 16)) <- eval (extract v_4 32 48);
      let v_14 <- eval (sub (sext v_12 18) (sext v_13 18));
      let (v_15 : expression (bv 16)) <- eval (extract v_14 2 18);
      let (v_16 : expression (bv 16)) <- eval (extract v_2 48 64);
      let (v_17 : expression (bv 16)) <- eval (extract v_4 48 64);
      let v_18 <- eval (sub (sext v_16 18) (sext v_17 18));
      let (v_19 : expression (bv 16)) <- eval (extract v_18 2 18);
      let (v_20 : expression (bv 16)) <- eval (extract v_2 64 80);
      let (v_21 : expression (bv 16)) <- eval (extract v_4 64 80);
      let v_22 <- eval (sub (sext v_20 18) (sext v_21 18));
      let (v_23 : expression (bv 16)) <- eval (extract v_22 2 18);
      let (v_24 : expression (bv 16)) <- eval (extract v_2 80 96);
      let (v_25 : expression (bv 16)) <- eval (extract v_4 80 96);
      let v_26 <- eval (sub (sext v_24 18) (sext v_25 18));
      let (v_27 : expression (bv 16)) <- eval (extract v_26 2 18);
      let (v_28 : expression (bv 16)) <- eval (extract v_2 96 112);
      let (v_29 : expression (bv 16)) <- eval (extract v_4 96 112);
      let v_30 <- eval (sub (sext v_28 18) (sext v_29 18));
      let (v_31 : expression (bv 16)) <- eval (extract v_30 2 18);
      let (v_32 : expression (bv 16)) <- eval (extract v_2 112 128);
      let (v_33 : expression (bv 16)) <- eval (extract v_4 112 128);
      let v_34 <- eval (sub (sext v_32 18) (sext v_33 18));
      let (v_35 : expression (bv 16)) <- eval (extract v_34 2 18);
      let v_36 <- eval (concat (mux (sgt v_30 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_30 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_31)) (mux (sgt v_34 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_34 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_35)));
      let v_37 <- eval (concat (mux (sgt v_26 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_26 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_27)) v_36);
      let v_38 <- eval (concat (mux (sgt v_22 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_22 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_23)) v_37);
      let v_39 <- eval (concat (mux (sgt v_18 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_18 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_19)) v_38);
      let v_40 <- eval (concat (mux (sgt v_14 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_15)) v_39);
      let v_41 <- eval (concat (mux (sgt v_10 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_10 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_11)) v_40);
      let v_42 <- eval (concat (mux (sgt v_6 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_6 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_7)) v_41);
      setRegister (lhs.of_reg xmm_1) v_42;
      pure ()
     action
