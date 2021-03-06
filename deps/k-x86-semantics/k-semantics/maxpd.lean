def maxpd : instruction :=
  definst "maxpd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 64)) <- eval (extract v_2 0 64);
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 16;
      let (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      let (v_7 : expression (bv 64)) <- eval (extract v_2 64 128);
      let (v_8 : expression (bv 64)) <- eval (extract v_5 64 128);
      let v_9 <- eval (concat (mux (eq (/- (_,_) -/  maxcmp_double v_3 v_6) (expression.bv_nat 1 1)) v_3 v_6) (mux (eq (/- (_,_) -/  maxcmp_double v_7 v_8) (expression.bv_nat 1 1)) v_7 v_8));
      setRegister (lhs.of_reg xmm_1) v_9;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 64)) <- eval (extract v_2 0 64);
      let v_4 <- getRegister (lhs.of_reg xmm_0);
      let (v_5 : expression (bv 64)) <- eval (extract v_4 0 64);
      let (v_6 : expression (bv 64)) <- eval (extract v_2 64 128);
      let (v_7 : expression (bv 64)) <- eval (extract v_4 64 128);
      let v_8 <- eval (concat (mux (eq (/- (_,_) -/  maxcmp_double v_3 v_5) (expression.bv_nat 1 1)) v_3 v_5) (mux (eq (/- (_,_) -/  maxcmp_double v_6 v_7) (expression.bv_nat 1 1)) v_6 v_7));
      setRegister (lhs.of_reg xmm_1) v_8;
      pure ()
     action
