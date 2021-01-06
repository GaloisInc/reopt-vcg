def movbe : instruction :=
  definst "movbe" $ do
    instr_pat $ fun (mem_0 : Mem) (r16_1 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 2;
      let (v_4 : expression (bv 8)) <- eval (extract v_3 8 16);
      let (v_5 : expression (bv 8)) <- eval (extract v_3 0 8);
      let v_6 <- eval (concat v_4 v_5);
      setRegister (lhs.of_reg r16_1) v_6;
      pure ()
     action;
    instr_pat $ fun (r16_0 : reg (bv 16)) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- getRegister (lhs.of_reg r16_0);
      let (v_4 : expression (bv 8)) <- eval (extract v_3 8 16);
      let (v_5 : expression (bv 8)) <- eval (extract v_3 0 8);
      let v_6 <- eval (concat v_4 v_5);
      store v_2 v_6 2;
      pure ()
     action
