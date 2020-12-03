def incl : instruction :=
  definst "incl" $ do
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- load v_1 4;
      let v_3 <- eval (add v_2 (expression.bv_nat 32 1));
      store v_1 v_3 4;
      let (v_5 : expression (bv 8)) <- eval (extract v_3 24 32);
      let (v_6 : expression (bv 31)) <- eval (extract v_2 1 32);
      let (v_7 : expression (bv 4)) <- eval (extract v_2 28 32);
      setRegister af (eq v_7 (expression.bv_nat 4 15));
      setRegister of (bit_and (isBitClear v_2 0) (eq v_6 (expression.bv_nat 31 2147483647)));
      setRegister pf (parityFlag v_5);
      setRegister sf (isBitSet v_3 0);
      setRegister zf (zeroFlag v_3);
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister (lhs.of_reg r32_0);
      let v_2 <- eval (add v_1 (expression.bv_nat 32 1));
      let (v_3 : expression (bv 8)) <- eval (extract v_2 24 32);
      let (v_4 : expression (bv 31)) <- eval (extract v_1 1 32);
      let (v_5 : expression (bv 4)) <- eval (extract v_1 28 32);
      setRegister (lhs.of_reg r32_0) v_2;
      setRegister af (eq v_5 (expression.bv_nat 4 15));
      setRegister of (bit_and (isBitClear v_1 0) (eq v_4 (expression.bv_nat 31 2147483647)));
      setRegister pf (parityFlag v_3);
      setRegister sf (isBitSet v_2 0);
      setRegister zf (zeroFlag v_2);
      pure ()
     action
