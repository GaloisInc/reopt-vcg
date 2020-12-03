def packusdw : instruction :=
  definst "packusdw" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let (v_5 : expression (bv 16)) <- eval (extract v_3 16 32);
      let (v_6 : expression (bv 32)) <- eval (extract v_3 32 64);
      let (v_7 : expression (bv 16)) <- eval (extract v_3 48 64);
      let (v_8 : expression (bv 32)) <- eval (extract v_3 64 96);
      let (v_9 : expression (bv 16)) <- eval (extract v_3 80 96);
      let (v_10 : expression (bv 32)) <- eval (extract v_3 96 128);
      let (v_11 : expression (bv 16)) <- eval (extract v_3 112 128);
      let v_12 <- getRegister (lhs.of_reg xmm_1);
      let (v_13 : expression (bv 32)) <- eval (extract v_12 0 32);
      let (v_14 : expression (bv 16)) <- eval (extract v_12 16 32);
      let (v_15 : expression (bv 32)) <- eval (extract v_12 32 64);
      let (v_16 : expression (bv 16)) <- eval (extract v_12 48 64);
      let (v_17 : expression (bv 32)) <- eval (extract v_12 64 96);
      let (v_18 : expression (bv 16)) <- eval (extract v_12 80 96);
      let (v_19 : expression (bv 32)) <- eval (extract v_12 96 128);
      let (v_20 : expression (bv 16)) <- eval (extract v_12 112 128);
      let v_21 <- eval (concat (mux (sgt v_17 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_17 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_18)) (mux (sgt v_19 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_19 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_20)));
      let v_22 <- eval (concat (mux (sgt v_15 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_15 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_16)) v_21);
      let v_23 <- eval (concat (mux (sgt v_13 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_13 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_14)) v_22);
      let v_24 <- eval (concat (mux (sgt v_10 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_10 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_11)) v_23);
      let v_25 <- eval (concat (mux (sgt v_8 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_8 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_9)) v_24);
      let v_26 <- eval (concat (mux (sgt v_6 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_7)) v_25);
      let v_27 <- eval (concat (mux (sgt v_4 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_4 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_5)) v_26);
      setRegister (lhs.of_reg xmm_1) v_27;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      let (v_4 : expression (bv 16)) <- eval (extract v_2 16 32);
      let (v_5 : expression (bv 32)) <- eval (extract v_2 32 64);
      let (v_6 : expression (bv 16)) <- eval (extract v_2 48 64);
      let (v_7 : expression (bv 32)) <- eval (extract v_2 64 96);
      let (v_8 : expression (bv 16)) <- eval (extract v_2 80 96);
      let (v_9 : expression (bv 32)) <- eval (extract v_2 96 128);
      let (v_10 : expression (bv 16)) <- eval (extract v_2 112 128);
      let v_11 <- getRegister (lhs.of_reg xmm_1);
      let (v_12 : expression (bv 32)) <- eval (extract v_11 0 32);
      let (v_13 : expression (bv 16)) <- eval (extract v_11 16 32);
      let (v_14 : expression (bv 32)) <- eval (extract v_11 32 64);
      let (v_15 : expression (bv 16)) <- eval (extract v_11 48 64);
      let (v_16 : expression (bv 32)) <- eval (extract v_11 64 96);
      let (v_17 : expression (bv 16)) <- eval (extract v_11 80 96);
      let (v_18 : expression (bv 32)) <- eval (extract v_11 96 128);
      let (v_19 : expression (bv 16)) <- eval (extract v_11 112 128);
      let v_20 <- eval (concat (mux (sgt v_16 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_16 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_17)) (mux (sgt v_18 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_18 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_19)));
      let v_21 <- eval (concat (mux (sgt v_14 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_14 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_15)) v_20);
      let v_22 <- eval (concat (mux (sgt v_12 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_13)) v_21);
      let v_23 <- eval (concat (mux (sgt v_9 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_10)) v_22);
      let v_24 <- eval (concat (mux (sgt v_7 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_8)) v_23);
      let v_25 <- eval (concat (mux (sgt v_5 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_6)) v_24);
      let v_26 <- eval (concat (mux (sgt v_3 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_3 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) v_4)) v_25);
      setRegister (lhs.of_reg xmm_1) v_26;
      pure ()
     action
