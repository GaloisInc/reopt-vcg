def negb : instruction :=
  definst "negb" $ do
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- load v_1 1;
      let v_3 <- eval (add (expression.bv_nat 8 1) (bv_xor v_2 (expression.bv_nat 8 255)));
      store v_1 v_3 1;
      let v_5 <- eval (isBitSet v_3 0);
      let (v_6 : expression (bv 8)) <- eval (extract v_3 0 8);
      setRegister af (notBool_ (eq (isBitSet v_2 3) (isBitSet v_3 3)));
      setRegister cf (notBool_ (eq v_2 (expression.bv_nat 8 0)));
      setRegister of (bit_and (isBitSet v_2 0) v_5);
      setRegister pf (parityFlag v_6);
      setRegister sf v_5;
      setRegister zf (zeroFlag v_3);
      pure ()
     action;
    instr_pat $ fun (rh_0 : reg (bv 8)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister (lhs.of_reg rh_0);
      let v_2 <- eval (add (expression.bv_nat 8 1) (bv_xor v_1 (expression.bv_nat 8 255)));
      let v_3 <- eval (isBitSet v_2 0);
      let (v_4 : expression (bv 8)) <- eval (extract v_2 0 8);
      setRegister (lhs.of_reg rh_0) v_2;
      setRegister af (notBool_ (eq (isBitSet v_1 3) (isBitSet v_2 3)));
      setRegister cf (notBool_ (eq v_1 (expression.bv_nat 8 0)));
      setRegister of (bit_and (isBitSet v_1 0) v_3);
      setRegister pf (parityFlag v_4);
      setRegister sf v_3;
      setRegister zf (zeroFlag v_2);
      pure ()
     action
