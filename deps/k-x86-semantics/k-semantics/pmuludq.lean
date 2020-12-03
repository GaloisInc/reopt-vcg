def pmuludq : instruction :=
  definst "pmuludq" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 32 64);
      let v_4 <- eval (concat (expression.bv_nat 32 0) v_3);
      let v_5 <- evaluateAddress mem_0;
      let v_6 <- load v_5 16;
      let (v_7 : expression (bv 32)) <- eval (extract v_6 32 64);
      let v_8 <- eval (concat (expression.bv_nat 32 0) v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_2 96 128);
      let v_10 <- eval (concat (expression.bv_nat 32 0) v_9);
      let (v_11 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_12 <- eval (concat (expression.bv_nat 32 0) v_11);
      let v_13 <- eval (concat (mul v_4 v_8) (mul v_10 v_12));
      setRegister (lhs.of_reg xmm_1) v_13;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 32 64);
      let v_4 <- eval (concat (expression.bv_nat 32 0) v_3);
      let v_5 <- getRegister (lhs.of_reg xmm_0);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 32 64);
      let v_7 <- eval (concat (expression.bv_nat 32 0) v_6);
      let (v_8 : expression (bv 32)) <- eval (extract v_2 96 128);
      let v_9 <- eval (concat (expression.bv_nat 32 0) v_8);
      let (v_10 : expression (bv 32)) <- eval (extract v_5 96 128);
      let v_11 <- eval (concat (expression.bv_nat 32 0) v_10);
      let v_12 <- eval (concat (mul v_4 v_7) (mul v_9 v_11));
      setRegister (lhs.of_reg xmm_1) v_12;
      pure ()
     action
