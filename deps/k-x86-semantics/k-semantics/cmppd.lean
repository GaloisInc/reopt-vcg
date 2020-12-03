def cmppd : instruction :=
  definst "cmppd" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_2);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let v_5 <- evaluateAddress mem_1;
      let v_6 <- load v_5 16;
      let (v_7 : expression (bv 64)) <- eval (extract v_6 0 64);
      let v_8 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_9 : expression (bv 64)) <- eval (extract v_3 64 128);
      let (v_10 : expression (bv 64)) <- eval (extract v_6 64 128);
      let v_11 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_double_pred v_4 v_7 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (/- (_,_,_) -/ cmp_double_pred v_9 v_10 v_8) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      setRegister (lhs.of_reg xmm_2) v_11;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_2);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      let v_7 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_8 : expression (bv 64)) <- eval (extract v_3 64 128);
      let (v_9 : expression (bv 64)) <- eval (extract v_5 64 128);
      let v_10 <- eval (concat (mux (eq (/- (_,_,_) -/ cmp_double_pred v_4 v_6 v_7) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (/- (_,_,_) -/ cmp_double_pred v_8 v_9 v_7) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      setRegister (lhs.of_reg xmm_2) v_10;
      pure ()
     action
