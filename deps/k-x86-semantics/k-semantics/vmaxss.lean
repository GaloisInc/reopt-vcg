def vmaxss : instruction :=
  definst "vmaxss" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 96)) <- eval (extract v_3 0 96);
      let (v_5 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_6 <- evaluateAddress mem_0;
      let v_7 <- load v_6 4;
      let v_8 <- eval (concat v_4 (mux (eq (/- (_,_) -/  maxcmp_single v_5 v_7) (expression.bv_nat 1 1)) v_5 v_7));
      setRegister (lhs.of_reg xmm_2) v_8;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 96)) <- eval (extract v_3 0 96);
      let (v_5 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_6 <- getRegister (lhs.of_reg xmm_0);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_8 <- eval (concat v_4 (mux (eq (/- (_,_) -/  maxcmp_single v_5 v_7) (expression.bv_nat 1 1)) v_5 v_7));
      setRegister (lhs.of_reg xmm_2) v_8;
      pure ()
     action
