def vmovsd : instruction :=
  definst "vmovsd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 8;
      let v_4 <- eval (concat (expression.bv_nat 64 0) v_3);
      setRegister (lhs.of_reg xmm_1) v_4;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- getRegister (lhs.of_reg xmm_0);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 64 128);
      store v_2 v_4 8;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let v_5 <- getRegister (lhs.of_reg xmm_0);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      let v_7 <- eval (concat v_4 v_6);
      setRegister (lhs.of_reg xmm_2) v_7;
      pure ()
     action
