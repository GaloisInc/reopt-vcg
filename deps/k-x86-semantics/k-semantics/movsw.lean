def movsw : instruction :=
  definst "movsw" $ do
    instr_pat $
     let action : semantics Unit := do
      let v_0 <- getRegister df;
      let v_1 <- eval (eq (eq (boolToBv1 v_0) (expression.bv_nat 1 0)) bit_one);
      let v_2 <- getRegister rdi;
      let v_3 <- getRegister rsi;
      let v_4 <- load v_3 2;
      store v_2 v_4 2;
      setRegister rdi (add v_2 (expression.bv_nat 64 2));
      setRegister rsi (add v_3 (expression.bv_nat 64 2));
      pure ()
     action;
    instr_pat $
     let action : semantics Unit := do
      let v_0 <- getRegister df;
      let v_1 <- eval (eq v_0 bit_one);
      let v_2 <- getRegister rdi;
      let v_3 <- getRegister rsi;
      let v_4 <- load v_3 2;
      store v_2 v_4 2;
      setRegister rdi (sub v_2 (expression.bv_nat 64 2));
      setRegister rsi (sub v_3 (expression.bv_nat 64 2));
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- getRegister df;
      let v_3 <- eval (eq (eq (boolToBv1 v_2) (expression.bv_nat 1 0)) bit_one);
      let v_4 <- getRegister rdi;
      let v_5 <- getRegister rsi;
      let v_6 <- load v_5 2;
      store v_4 v_6 2;
      setRegister rdi (add v_4 (expression.bv_nat 64 2));
      setRegister rsi (add v_5 (expression.bv_nat 64 2));
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- getRegister df;
      let v_3 <- eval (eq v_2 bit_one);
      let v_4 <- getRegister rdi;
      let v_5 <- getRegister rsi;
      let v_6 <- load v_5 2;
      store v_4 v_6 2;
      setRegister rdi (sub v_4 (expression.bv_nat 64 2));
      setRegister rsi (sub v_5 (expression.bv_nat 64 2));
      pure ()
     action
