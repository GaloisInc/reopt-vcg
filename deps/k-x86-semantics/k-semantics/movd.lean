def movd : instruction :=
  definst "movd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 4;
      let v_4 <- eval (concat (expression.bv_nat 96 0) v_3);
      setRegister (lhs.of_reg xmm_1) v_4;
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r32_0);
      let v_3 <- eval (concat (expression.bv_nat 96 0) v_2);
      setRegister (lhs.of_reg xmm_1) v_3;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- getRegister (lhs.of_reg xmm_0);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 96 128);
      store v_2 v_4 4;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 96 128);
      setRegister (lhs.of_reg r32_1) v_3;
      pure ()
     action
