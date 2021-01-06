def pmovzxdq : instruction :=
  definst "pmovzxdq" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 8;
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let (v_5 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_6 <- eval (concat (expression.bv_nat 32 0) v_5);
      let v_7 <- eval (concat v_4 v_6);
      let v_8 <- eval (concat (expression.bv_nat 32 0) v_7);
      setRegister (lhs.of_reg xmm_1) v_8;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 64 96);
      let (v_4 : expression (bv 32)) <- eval (extract v_2 96 128);
      let v_5 <- eval (concat (expression.bv_nat 32 0) v_4);
      let v_6 <- eval (concat v_3 v_5);
      let v_7 <- eval (concat (expression.bv_nat 32 0) v_6);
      setRegister (lhs.of_reg xmm_1) v_7;
      pure ()
     action
