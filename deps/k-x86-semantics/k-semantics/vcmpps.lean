def vcmpps : instruction :=
  definst "vcmpps" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_4 <- getRegister (lhs.of_reg xmm_2);
      let (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      let v_6 <- evaluateAddress mem_1;
      let v_7 <- load v_6 16;
      let (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      let v_9 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_10 : expression (bv 32)) <- eval (extract v_4 32 64);
      let (v_11 : expression (bv 32)) <- eval (extract v_7 32 64);
      let (v_12 : expression (bv 32)) <- eval (extract v_4 64 96);
      let (v_13 : expression (bv 32)) <- eval (extract v_7 64 96);
      let (v_14 : expression (bv 32)) <- eval (extract v_4 96 128);
      let (v_15 : expression (bv 32)) <- eval (extract v_7 96 128);
      let v_16 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_12 v_13 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (/- (_,_,_) -/ cmp_single_pred v_14 v_15 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)));
      let v_17 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_10 v_11 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) v_16);
      let v_18 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_5 v_8 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) v_17);
      setRegister (lhs.of_reg xmm_3) v_18;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_4 <- getRegister (lhs.of_reg ymm_2);
      let (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      let v_6 <- evaluateAddress mem_1;
      let v_7 <- load v_6 32;
      let (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      let v_9 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_10 : expression (bv 32)) <- eval (extract v_4 32 64);
      let (v_11 : expression (bv 32)) <- eval (extract v_7 32 64);
      let (v_12 : expression (bv 32)) <- eval (extract v_4 64 96);
      let (v_13 : expression (bv 32)) <- eval (extract v_7 64 96);
      let (v_14 : expression (bv 32)) <- eval (extract v_4 96 128);
      let (v_15 : expression (bv 32)) <- eval (extract v_7 96 128);
      let (v_16 : expression (bv 32)) <- eval (extract v_4 128 160);
      let (v_17 : expression (bv 32)) <- eval (extract v_7 128 160);
      let (v_18 : expression (bv 32)) <- eval (extract v_4 160 192);
      let (v_19 : expression (bv 32)) <- eval (extract v_7 160 192);
      let (v_20 : expression (bv 32)) <- eval (extract v_4 192 224);
      let (v_21 : expression (bv 32)) <- eval (extract v_7 192 224);
      let (v_22 : expression (bv 32)) <- eval (extract v_4 224 256);
      let (v_23 : expression (bv 32)) <- eval (extract v_7 224 256);
      let v_24 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_20 v_21 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (/- (_,_,_) -/ cmp_single_pred v_22 v_23 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)));
      let v_25 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_18 v_19 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) v_24);
      let v_26 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_16 v_17 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) v_25);
      let v_27 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_14 v_15 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) v_26);
      let v_28 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_12 v_13 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) v_27);
      let v_29 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_10 v_11 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) v_28);
      let v_30 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_5 v_8 v_9) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) v_29);
      setRegister (lhs.of_reg ymm_3) v_30;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_4 <- getRegister (lhs.of_reg xmm_2);
      let (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      let v_6 <- getRegister (lhs.of_reg xmm_1);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      let v_8 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_9 : expression (bv 32)) <- eval (extract v_4 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract v_6 32 64);
      let (v_11 : expression (bv 32)) <- eval (extract v_4 64 96);
      let (v_12 : expression (bv 32)) <- eval (extract v_6 64 96);
      let (v_13 : expression (bv 32)) <- eval (extract v_4 96 128);
      let (v_14 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_15 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_11 v_12 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (/- (_,_,_) -/ cmp_single_pred v_13 v_14 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)));
      let v_16 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_9 v_10 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) v_15);
      let v_17 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_5 v_7 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) v_16);
      setRegister (lhs.of_reg xmm_3) v_17;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_4 <- getRegister (lhs.of_reg ymm_2);
      let (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      let v_6 <- getRegister (lhs.of_reg ymm_1);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      let v_8 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_9 : expression (bv 32)) <- eval (extract v_4 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract v_6 32 64);
      let (v_11 : expression (bv 32)) <- eval (extract v_4 64 96);
      let (v_12 : expression (bv 32)) <- eval (extract v_6 64 96);
      let (v_13 : expression (bv 32)) <- eval (extract v_4 96 128);
      let (v_14 : expression (bv 32)) <- eval (extract v_6 96 128);
      let (v_15 : expression (bv 32)) <- eval (extract v_4 128 160);
      let (v_16 : expression (bv 32)) <- eval (extract v_6 128 160);
      let (v_17 : expression (bv 32)) <- eval (extract v_4 160 192);
      let (v_18 : expression (bv 32)) <- eval (extract v_6 160 192);
      let (v_19 : expression (bv 32)) <- eval (extract v_4 192 224);
      let (v_20 : expression (bv 32)) <- eval (extract v_6 192 224);
      let (v_21 : expression (bv 32)) <- eval (extract v_4 224 256);
      let (v_22 : expression (bv 32)) <- eval (extract v_6 224 256);
      let v_23 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_19 v_20 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (/- (_,_,_) -/ cmp_single_pred v_21 v_22 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)));
      let v_24 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_17 v_18 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) v_23);
      let v_25 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_15 v_16 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) v_24);
      let v_26 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_13 v_14 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) v_25);
      let v_27 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_11 v_12 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) v_26);
      let v_28 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_9 v_10 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) v_27);
      let v_29 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_5 v_7 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) v_28);
      setRegister (lhs.of_reg ymm_3) v_29;
      pure ()
     action
