def blsrl : instruction :=
  definst "blsrl" $ do
    instr_pat $ fun (mem_0 : Mem) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 4;
      let v_4 <- eval (bv_and (sub v_3 (expression.bv_nat 32 1)) v_3);
      setRegister (lhs.of_reg r32_1) v_4;
      setRegister af undef;
      setRegister cf (eq v_3 (expression.bv_nat 32 0));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_4 0);
      setRegister zf (zeroFlag v_4);
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r32_0);
      let v_3 <- eval (bv_and (sub v_2 (expression.bv_nat 32 1)) v_2);
      setRegister (lhs.of_reg r32_1) v_3;
      setRegister af undef;
      setRegister cf (eq v_2 (expression.bv_nat 32 0));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_3 0);
      setRegister zf (zeroFlag v_3);
      pure ()
     action
