def movbel : instruction :=
  definst "movbel" $ do
    instr_pat $ fun (mem_0 : Mem) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 4;
      let (v_4 : expression (bv 8)) <- eval (extract v_3 24 32);
      let (v_5 : expression (bv 8)) <- eval (extract v_3 16 24);
      let v_6 <- eval (concat v_4 v_5);
      let (v_7 : expression (bv 8)) <- eval (extract v_3 8 16);
      let v_8 <- eval (concat v_6 v_7);
      let (v_9 : expression (bv 8)) <- eval (extract v_3 0 8);
      let v_10 <- eval (concat v_8 v_9);
      setRegister (lhs.of_reg r32_1) v_10;
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- getRegister (lhs.of_reg r32_0);
      let (v_4 : expression (bv 8)) <- eval (extract v_3 24 32);
      let (v_5 : expression (bv 8)) <- eval (extract v_3 16 24);
      let v_6 <- eval (concat v_4 v_5);
      let (v_7 : expression (bv 8)) <- eval (extract v_3 8 16);
      let v_8 <- eval (concat v_6 v_7);
      let (v_9 : expression (bv 8)) <- eval (extract v_3 0 8);
      let v_10 <- eval (concat v_8 v_9);
      store v_2 v_10 4;
      pure ()
     action
