def pmovzxwd : instruction :=
  definst "pmovzxwd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 8;
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let (v_5 : expression (bv 16)) <- eval (extract v_3 16 32);
      let (v_6 : expression (bv 16)) <- eval (extract v_3 32 48);
      let (v_7 : expression (bv 16)) <- eval (extract v_3 48 64);
      let v_8 <- eval (concat (expression.bv_nat 16 0) v_7);
      let v_9 <- eval (concat v_6 v_8);
      let v_10 <- eval (concat (expression.bv_nat 16 0) v_9);
      let v_11 <- eval (concat v_5 v_10);
      let v_12 <- eval (concat (expression.bv_nat 16 0) v_11);
      let v_13 <- eval (concat v_4 v_12);
      let v_14 <- eval (concat (expression.bv_nat 16 0) v_13);
      setRegister (lhs.of_reg xmm_1) v_14;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 16)) <- eval (extract v_2 64 80);
      let (v_4 : expression (bv 16)) <- eval (extract v_2 80 96);
      let (v_5 : expression (bv 16)) <- eval (extract v_2 96 112);
      let (v_6 : expression (bv 16)) <- eval (extract v_2 112 128);
      let v_7 <- eval (concat (expression.bv_nat 16 0) v_6);
      let v_8 <- eval (concat v_5 v_7);
      let v_9 <- eval (concat (expression.bv_nat 16 0) v_8);
      let v_10 <- eval (concat v_4 v_9);
      let v_11 <- eval (concat (expression.bv_nat 16 0) v_10);
      let v_12 <- eval (concat v_3 v_11);
      let v_13 <- eval (concat (expression.bv_nat 16 0) v_12);
      setRegister (lhs.of_reg xmm_1) v_13;
      pure ()
     action
