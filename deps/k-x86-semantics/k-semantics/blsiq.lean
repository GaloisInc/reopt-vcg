def blsiq : instruction :=
  definst "blsiq" $ do
    instr_pat $ fun (mem_0 : Mem) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 8;
      let v_4 <- eval (bv_and (add (expression.bv_nat 64 1) (bv_xor v_3 (expression.bv_nat 64 18446744073709551615))) v_3);
      setRegister (lhs.of_reg r64_1) v_4;
      setRegister af undef;
      setRegister cf (notBool_ (eq v_3 (expression.bv_nat 64 0)));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_4 0);
      setRegister zf (zeroFlag v_4);
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r64_0);
      let v_3 <- eval (bv_and (add (expression.bv_nat 64 1) (bv_xor v_2 (expression.bv_nat 64 18446744073709551615))) v_2);
      setRegister (lhs.of_reg r64_1) v_3;
      setRegister af undef;
      setRegister cf (notBool_ (eq v_2 (expression.bv_nat 64 0)));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_3 0);
      setRegister zf (zeroFlag v_3);
      pure ()
     action
