def decw : instruction :=
  definst "decw" $ do
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- load v_1 2;
      let v_3 <- eval (sub v_2 (expression.bv_nat 16 1));
      store v_1 v_3 2;
      let (v_5 : expression (bv 8)) <- eval (extract v_3 8 16);
      let (v_6 : expression (bv 15)) <- eval (extract v_2 1 16);
      let (v_7 : expression (bv 4)) <- eval (extract v_2 12 16);
      setRegister af (eq v_7 (expression.bv_nat 4 0));
      setRegister of (bit_and (isBitSet v_2 0) (eq v_6 (expression.bv_nat 15 0)));
      setRegister pf (parityFlag v_5);
      setRegister sf (isBitSet v_3 0);
      setRegister zf (zeroFlag v_3);
      pure ()
     action;
    instr_pat $ fun (r16_0 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister (lhs.of_reg r16_0);
      let v_2 <- eval (sub v_1 (expression.bv_nat 16 1));
      let (v_3 : expression (bv 8)) <- eval (extract v_2 8 16);
      let (v_4 : expression (bv 15)) <- eval (extract v_1 1 16);
      let (v_5 : expression (bv 4)) <- eval (extract v_1 12 16);
      setRegister (lhs.of_reg r16_0) v_2;
      setRegister af (eq v_5 (expression.bv_nat 4 0));
      setRegister of (bit_and (isBitSet v_1 0) (eq v_4 (expression.bv_nat 15 0)));
      setRegister pf (parityFlag v_3);
      setRegister sf (isBitSet v_2 0);
      setRegister zf (zeroFlag v_2);
      pure ()
     action
