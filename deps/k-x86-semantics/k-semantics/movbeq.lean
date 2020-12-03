def movbeq : instruction :=
  definst "movbeq" $ do
    instr_pat $ fun (mem_0 : Mem) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 8;
      let (v_4 : expression (bv 8)) <- eval (extract v_3 56 64);
      let (v_5 : expression (bv 8)) <- eval (extract v_3 48 56);
      let v_6 <- eval (concat v_4 v_5);
      let (v_7 : expression (bv 8)) <- eval (extract v_3 40 48);
      let v_8 <- eval (concat v_6 v_7);
      let (v_9 : expression (bv 8)) <- eval (extract v_3 32 40);
      let v_10 <- eval (concat v_8 v_9);
      let (v_11 : expression (bv 8)) <- eval (extract v_3 24 32);
      let v_12 <- eval (concat v_10 v_11);
      let (v_13 : expression (bv 8)) <- eval (extract v_3 16 24);
      let v_14 <- eval (concat v_12 v_13);
      let (v_15 : expression (bv 8)) <- eval (extract v_3 8 16);
      let v_16 <- eval (concat v_14 v_15);
      let (v_17 : expression (bv 8)) <- eval (extract v_3 0 8);
      let v_18 <- eval (concat v_16 v_17);
      setRegister (lhs.of_reg r64_1) v_18;
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- getRegister (lhs.of_reg r64_0);
      let (v_4 : expression (bv 8)) <- eval (extract v_3 56 64);
      let (v_5 : expression (bv 8)) <- eval (extract v_3 48 56);
      let v_6 <- eval (concat v_4 v_5);
      let (v_7 : expression (bv 8)) <- eval (extract v_3 40 48);
      let v_8 <- eval (concat v_6 v_7);
      let (v_9 : expression (bv 8)) <- eval (extract v_3 32 40);
      let v_10 <- eval (concat v_8 v_9);
      let (v_11 : expression (bv 8)) <- eval (extract v_3 24 32);
      let v_12 <- eval (concat v_10 v_11);
      let (v_13 : expression (bv 8)) <- eval (extract v_3 16 24);
      let v_14 <- eval (concat v_12 v_13);
      let (v_15 : expression (bv 8)) <- eval (extract v_3 8 16);
      let v_16 <- eval (concat v_14 v_15);
      let (v_17 : expression (bv 8)) <- eval (extract v_3 0 8);
      let v_18 <- eval (concat v_16 v_17);
      store v_2 v_18 8;
      pure ()
     action
