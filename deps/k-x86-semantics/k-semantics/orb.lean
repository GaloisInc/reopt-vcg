def orb : instruction :=
  definst "orb" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- load v_2 1;
      let v_4 <- eval (bv_or v_3 (handleImmediateWithSignExtend imm_0 8 8));
      store v_2 v_4 1;
      let (v_6 : expression (bv 8)) <- eval (extract v_4 0 8);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag v_6);
      setRegister sf (isBitSet v_4 0);
      setRegister zf (zeroFlag v_4);
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (rh_1 : reg (bv 8)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg rh_1);
      let v_3 <- eval (bv_or v_2 (handleImmediateWithSignExtend imm_0 8 8));
      let (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      setRegister (lhs.of_reg rh_1) v_3;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag v_4);
      setRegister sf (isBitSet v_3 0);
      setRegister zf (zeroFlag v_3);
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (rh_1 : reg (bv 8)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg rh_1);
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 1;
      let v_5 <- eval (bv_or v_2 v_4);
      let (v_6 : expression (bv 8)) <- eval (extract v_5 0 8);
      setRegister (lhs.of_reg rh_1) v_5;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag v_6);
      setRegister sf (isBitSet v_5 0);
      setRegister zf (zeroFlag v_5);
      pure ()
     action;
    instr_pat $ fun (rh_0 : reg (bv 8)) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- load v_2 1;
      let v_4 <- getRegister (lhs.of_reg rh_0);
      let v_5 <- eval (bv_or v_3 v_4);
      store v_2 v_5 1;
      let (v_7 : expression (bv 8)) <- eval (extract v_5 0 8);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag v_7);
      setRegister sf (isBitSet v_5 0);
      setRegister zf (zeroFlag v_5);
      pure ()
     action;
    instr_pat $ fun (rh_0 : reg (bv 8)) (rh_1 : reg (bv 8)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg rh_1);
      let v_3 <- getRegister (lhs.of_reg rh_0);
      let v_4 <- eval (bv_or v_2 v_3);
      let (v_5 : expression (bv 8)) <- eval (extract v_4 0 8);
      setRegister (lhs.of_reg rh_1) v_4;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag v_5);
      setRegister sf (isBitSet v_4 0);
      setRegister zf (zeroFlag v_4);
      pure ()
     action
