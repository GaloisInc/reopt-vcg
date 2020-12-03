def minps : instruction :=
  definst "minps" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 16;
      let (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      let (v_7 : expression (bv 32)) <- eval (extract v_2 32 64);
      let (v_8 : expression (bv 32)) <- eval (extract v_5 32 64);
      let (v_9 : expression (bv 32)) <- eval (extract v_2 64 96);
      let (v_10 : expression (bv 32)) <- eval (extract v_5 64 96);
      let (v_11 : expression (bv 32)) <- eval (extract v_2 96 128);
      let (v_12 : expression (bv 32)) <- eval (extract v_5 96 128);
      let v_13 <- eval (concat (mux (eq (/- (_,_) -/  mincmp_single v_9 v_10) (expression.bv_nat 1 1)) v_9 v_10) (mux (eq (/- (_,_) -/  mincmp_single v_11 v_12) (expression.bv_nat 1 1)) v_11 v_12));
      let v_14 <- eval (concat (mux (eq (/- (_,_) -/  mincmp_single v_7 v_8) (expression.bv_nat 1 1)) v_7 v_8) v_13);
      let v_15 <- eval (concat (mux (eq (/- (_,_) -/  mincmp_single v_3 v_6) (expression.bv_nat 1 1)) v_3 v_6) v_14);
      setRegister (lhs.of_reg xmm_1) v_15;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      let v_4 <- getRegister (lhs.of_reg xmm_0);
      let (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      let (v_6 : expression (bv 32)) <- eval (extract v_2 32 64);
      let (v_7 : expression (bv 32)) <- eval (extract v_4 32 64);
      let (v_8 : expression (bv 32)) <- eval (extract v_2 64 96);
      let (v_9 : expression (bv 32)) <- eval (extract v_4 64 96);
      let (v_10 : expression (bv 32)) <- eval (extract v_2 96 128);
      let (v_11 : expression (bv 32)) <- eval (extract v_4 96 128);
      let v_12 <- eval (concat (mux (eq (/- (_,_) -/  mincmp_single v_8 v_9) (expression.bv_nat 1 1)) v_8 v_9) (mux (eq (/- (_,_) -/  mincmp_single v_10 v_11) (expression.bv_nat 1 1)) v_10 v_11));
      let v_13 <- eval (concat (mux (eq (/- (_,_) -/  mincmp_single v_6 v_7) (expression.bv_nat 1 1)) v_6 v_7) v_12);
      let v_14 <- eval (concat (mux (eq (/- (_,_) -/  mincmp_single v_3 v_5) (expression.bv_nat 1 1)) v_3 v_5) v_13);
      setRegister (lhs.of_reg xmm_1) v_14;
      pure ()
     action
