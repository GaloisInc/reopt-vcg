def psignd : instruction :=
  definst "psignd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      let (v_7 : expression (bv 32)) <- eval (extract v_3 32 64);
      let (v_8 : expression (bv 32)) <- eval (extract v_5 32 64);
      let (v_9 : expression (bv 32)) <- eval (extract v_3 64 96);
      let (v_10 : expression (bv 32)) <- eval (extract v_5 64 96);
      let (v_11 : expression (bv 32)) <- eval (extract v_3 96 128);
      let (v_12 : expression (bv 32)) <- eval (extract v_5 96 128);
      let v_13 <- eval (concat (mux (sgt v_9 (expression.bv_nat 32 0)) v_10 (mux (eq v_9 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_10 (expression.bv_nat 32 4294967295))))) (mux (sgt v_11 (expression.bv_nat 32 0)) v_12 (mux (eq v_11 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_12 (expression.bv_nat 32 4294967295))))));
      let v_14 <- eval (concat (mux (sgt v_7 (expression.bv_nat 32 0)) v_8 (mux (eq v_7 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_8 (expression.bv_nat 32 4294967295))))) v_13);
      let v_15 <- eval (concat (mux (sgt v_4 (expression.bv_nat 32 0)) v_6 (mux (eq v_4 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_6 (expression.bv_nat 32 4294967295))))) v_14);
      setRegister (lhs.of_reg xmm_1) v_15;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      let v_4 <- getRegister (lhs.of_reg xmm_1);
      let (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      let (v_6 : expression (bv 32)) <- eval (extract v_2 32 64);
      let (v_7 : expression (bv 32)) <- eval (extract v_4 32 64);
      let (v_8 : expression (bv 32)) <- eval (extract v_2 64 96);
      let (v_9 : expression (bv 32)) <- eval (extract v_4 64 96);
      let (v_10 : expression (bv 32)) <- eval (extract v_2 96 128);
      let (v_11 : expression (bv 32)) <- eval (extract v_4 96 128);
      let v_12 <- eval (concat (mux (sgt v_8 (expression.bv_nat 32 0)) v_9 (mux (eq v_8 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_9 (expression.bv_nat 32 4294967295))))) (mux (sgt v_10 (expression.bv_nat 32 0)) v_11 (mux (eq v_10 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_11 (expression.bv_nat 32 4294967295))))));
      let v_13 <- eval (concat (mux (sgt v_6 (expression.bv_nat 32 0)) v_7 (mux (eq v_6 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7 (expression.bv_nat 32 4294967295))))) v_12);
      let v_14 <- eval (concat (mux (sgt v_3 (expression.bv_nat 32 0)) v_5 (mux (eq v_3 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_5 (expression.bv_nat 32 4294967295))))) v_13);
      setRegister (lhs.of_reg xmm_1) v_14;
      pure ()
     action
