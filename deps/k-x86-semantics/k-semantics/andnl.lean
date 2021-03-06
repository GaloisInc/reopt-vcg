def andnl : instruction :=
  definst "andnl" $ do
    instr_pat $ fun (mem_0 : Mem) (r32_1 : reg (bv 32)) (r32_2 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg r32_1);
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 4;
      let v_6 <- eval (bv_and (bv_xor v_3 (expression.bv_nat 32 4294967295)) v_5);
      setRegister (lhs.of_reg r32_2) v_6;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (bit_and (notBool_ (eq (isBitSet v_3 0) (bv1ToBool (expression.bv_nat 1 1)))) (isBitSet v_5 0));
      setRegister zf (zeroFlag v_6);
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) (r32_2 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg r32_1);
      let v_4 <- getRegister (lhs.of_reg r32_0);
      let v_5 <- eval (bv_and (bv_xor v_3 (expression.bv_nat 32 4294967295)) v_4);
      setRegister (lhs.of_reg r32_2) v_5;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (bit_and (notBool_ (eq (isBitSet v_3 0) (bv1ToBool (expression.bv_nat 1 1)))) (isBitSet v_4 0));
      setRegister zf (zeroFlag v_5);
      pure ()
     action
