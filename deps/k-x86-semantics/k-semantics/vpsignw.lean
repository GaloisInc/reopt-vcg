def vpsignw : instruction :=
  definst "vpsignw" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 16;
      let (v_5 : expression (bv 16)) <- eval (extract v_4 0 16);
      let v_6 <- getRegister (lhs.of_reg xmm_1);
      let (v_7 : expression (bv 16)) <- eval (extract v_6 0 16);
      let (v_8 : expression (bv 16)) <- eval (extract v_4 16 32);
      let (v_9 : expression (bv 16)) <- eval (extract v_6 16 32);
      let (v_10 : expression (bv 16)) <- eval (extract v_4 32 48);
      let (v_11 : expression (bv 16)) <- eval (extract v_6 32 48);
      let (v_12 : expression (bv 16)) <- eval (extract v_4 48 64);
      let (v_13 : expression (bv 16)) <- eval (extract v_6 48 64);
      let (v_14 : expression (bv 16)) <- eval (extract v_4 64 80);
      let (v_15 : expression (bv 16)) <- eval (extract v_6 64 80);
      let (v_16 : expression (bv 16)) <- eval (extract v_4 80 96);
      let (v_17 : expression (bv 16)) <- eval (extract v_6 80 96);
      let (v_18 : expression (bv 16)) <- eval (extract v_4 96 112);
      let (v_19 : expression (bv 16)) <- eval (extract v_6 96 112);
      let (v_20 : expression (bv 16)) <- eval (extract v_4 112 128);
      let (v_21 : expression (bv 16)) <- eval (extract v_6 112 128);
      let v_22 <- eval (concat (mux (sgt v_18 (expression.bv_nat 16 0)) v_19 (mux (eq v_18 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_19 (expression.bv_nat 16 65535))))) (mux (sgt v_20 (expression.bv_nat 16 0)) v_21 (mux (eq v_20 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_21 (expression.bv_nat 16 65535))))));
      let v_23 <- eval (concat (mux (sgt v_16 (expression.bv_nat 16 0)) v_17 (mux (eq v_16 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_17 (expression.bv_nat 16 65535))))) v_22);
      let v_24 <- eval (concat (mux (sgt v_14 (expression.bv_nat 16 0)) v_15 (mux (eq v_14 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_15 (expression.bv_nat 16 65535))))) v_23);
      let v_25 <- eval (concat (mux (sgt v_12 (expression.bv_nat 16 0)) v_13 (mux (eq v_12 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_13 (expression.bv_nat 16 65535))))) v_24);
      let v_26 <- eval (concat (mux (sgt v_10 (expression.bv_nat 16 0)) v_11 (mux (eq v_10 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_11 (expression.bv_nat 16 65535))))) v_25);
      let v_27 <- eval (concat (mux (sgt v_8 (expression.bv_nat 16 0)) v_9 (mux (eq v_8 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_9 (expression.bv_nat 16 65535))))) v_26);
      let v_28 <- eval (concat (mux (sgt v_5 (expression.bv_nat 16 0)) v_7 (mux (eq v_5 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7 (expression.bv_nat 16 65535))))) v_27);
      setRegister (lhs.of_reg xmm_2) v_28;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_0);
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      let (v_7 : expression (bv 16)) <- eval (extract v_3 16 32);
      let (v_8 : expression (bv 16)) <- eval (extract v_5 16 32);
      let (v_9 : expression (bv 16)) <- eval (extract v_3 32 48);
      let (v_10 : expression (bv 16)) <- eval (extract v_5 32 48);
      let (v_11 : expression (bv 16)) <- eval (extract v_3 48 64);
      let (v_12 : expression (bv 16)) <- eval (extract v_5 48 64);
      let (v_13 : expression (bv 16)) <- eval (extract v_3 64 80);
      let (v_14 : expression (bv 16)) <- eval (extract v_5 64 80);
      let (v_15 : expression (bv 16)) <- eval (extract v_3 80 96);
      let (v_16 : expression (bv 16)) <- eval (extract v_5 80 96);
      let (v_17 : expression (bv 16)) <- eval (extract v_3 96 112);
      let (v_18 : expression (bv 16)) <- eval (extract v_5 96 112);
      let (v_19 : expression (bv 16)) <- eval (extract v_3 112 128);
      let (v_20 : expression (bv 16)) <- eval (extract v_5 112 128);
      let v_21 <- eval (concat (mux (sgt v_17 (expression.bv_nat 16 0)) v_18 (mux (eq v_17 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_18 (expression.bv_nat 16 65535))))) (mux (sgt v_19 (expression.bv_nat 16 0)) v_20 (mux (eq v_19 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_20 (expression.bv_nat 16 65535))))));
      let v_22 <- eval (concat (mux (sgt v_15 (expression.bv_nat 16 0)) v_16 (mux (eq v_15 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_16 (expression.bv_nat 16 65535))))) v_21);
      let v_23 <- eval (concat (mux (sgt v_13 (expression.bv_nat 16 0)) v_14 (mux (eq v_13 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14 (expression.bv_nat 16 65535))))) v_22);
      let v_24 <- eval (concat (mux (sgt v_11 (expression.bv_nat 16 0)) v_12 (mux (eq v_11 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_12 (expression.bv_nat 16 65535))))) v_23);
      let v_25 <- eval (concat (mux (sgt v_9 (expression.bv_nat 16 0)) v_10 (mux (eq v_9 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_10 (expression.bv_nat 16 65535))))) v_24);
      let v_26 <- eval (concat (mux (sgt v_7 (expression.bv_nat 16 0)) v_8 (mux (eq v_7 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_8 (expression.bv_nat 16 65535))))) v_25);
      let v_27 <- eval (concat (mux (sgt v_4 (expression.bv_nat 16 0)) v_6 (mux (eq v_4 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_6 (expression.bv_nat 16 65535))))) v_26);
      setRegister (lhs.of_reg xmm_2) v_27;
      pure ()
     action
