def vminsd : instruction :=
  definst "vminsd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let (v_5 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_6 <- evaluateAddress mem_0;
      let v_7 <- load v_6 8;
      let v_8 <- eval (concat v_4 (mux (eq (/- (_,_) -/  mincmp_double v_5 v_7) (expression.bv_nat 1 1)) v_5 v_7));
      setRegister (lhs.of_reg xmm_2) v_8;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let (v_5 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_6 <- getRegister (lhs.of_reg xmm_0);
      let (v_7 : expression (bv 64)) <- eval (extract v_6 64 128);
      let v_8 <- eval (concat v_4 (mux (eq (/- (_,_) -/  mincmp_double v_5 v_7) (expression.bv_nat 1 1)) v_5 v_7));
      setRegister (lhs.of_reg xmm_2) v_8;
      pure ()
     action
