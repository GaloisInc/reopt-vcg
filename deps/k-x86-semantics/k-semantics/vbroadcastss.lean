def vbroadcastss : instruction :=
  definst "vbroadcastss" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 4;
      let v_4 <- eval (concat v_3 v_3);
      let v_5 <- eval (concat v_4 v_3);
      let v_6 <- eval (concat v_5 v_3);
      setRegister (lhs.of_reg xmm_1) v_6;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 4;
      let v_4 <- eval (concat v_3 v_3);
      let v_5 <- eval (concat v_4 v_3);
      let v_6 <- eval (concat v_5 v_3);
      let v_7 <- eval (concat v_6 v_3);
      let v_8 <- eval (concat v_7 v_3);
      let v_9 <- eval (concat v_8 v_3);
      let v_10 <- eval (concat v_9 v_3);
      setRegister (lhs.of_reg ymm_1) v_10;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 96 128);
      let v_4 <- eval (concat v_3 v_3);
      let v_5 <- eval (concat v_4 v_3);
      let v_6 <- eval (concat v_5 v_3);
      setRegister (lhs.of_reg xmm_1) v_6;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 96 128);
      let v_4 <- eval (concat v_3 v_3);
      let v_5 <- eval (concat v_4 v_3);
      let v_6 <- eval (concat v_5 v_3);
      let v_7 <- eval (concat v_6 v_3);
      let v_8 <- eval (concat v_7 v_3);
      let v_9 <- eval (concat v_8 v_3);
      let v_10 <- eval (concat v_9 v_3);
      setRegister (lhs.of_reg ymm_1) v_10;
      pure ()
     action
