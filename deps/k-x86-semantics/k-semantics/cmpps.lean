def cmpps : instruction :=
  definst "cmpps" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_2);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- evaluateAddress mem_1;
      let v_6 <- load v_5 16;
      let (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      let v_8 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_9 : expression (bv 32)) <- eval (extract v_3 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract v_6 32 64);
      let (v_11 : expression (bv 32)) <- eval (extract v_3 64 96);
      let (v_12 : expression (bv 32)) <- eval (extract v_6 64 96);
      let (v_13 : expression (bv 32)) <- eval (extract v_3 96 128);
      let (v_14 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_15 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_11 v_12 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (/- (_,_,_) -/ cmp_single_pred v_13 v_14 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)));
      let v_16 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_9 v_10 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) v_15);
      let v_17 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_4 v_7 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) v_16);
      setRegister (lhs.of_reg xmm_2) v_17;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_2);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      let v_7 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_8 : expression (bv 32)) <- eval (extract v_3 32 64);
      let (v_9 : expression (bv 32)) <- eval (extract v_5 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract v_3 64 96);
      let (v_11 : expression (bv 32)) <- eval (extract v_5 64 96);
      let (v_12 : expression (bv 32)) <- eval (extract v_3 96 128);
      let (v_13 : expression (bv 32)) <- eval (extract v_5 96 128);
      let v_14 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_10 v_11 v_7) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (/- (_,_,_) -/ cmp_single_pred v_12 v_13 v_7) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)));
      let v_15 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_8 v_9 v_7) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) v_14);
      let v_16 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_single_pred v_4 v_6 v_7) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) v_15);
      setRegister (lhs.of_reg xmm_2) v_16;
      pure ()
     action
