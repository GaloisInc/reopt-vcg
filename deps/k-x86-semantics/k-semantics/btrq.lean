def btrq : instruction :=
  definst "btrq" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_4 : expression (bv 5)) <- eval (extract v_3 0 5);
      let v_5 <- eval (concat (expression.bv_nat 59 0) (bv_and v_4 (expression.bv_nat 5 7)));
      let v_6 <- eval (add v_2 v_5);
      let v_7 <- load v_6 1;
      let (v_8 : expression (bv 3)) <- eval (extract v_3 5 8);
      let v_9 <- eval (concat (expression.bv_nat 5 0) (bv_and v_8 (expression.bv_nat 3 7)));
      let (v_10 : expression (bv 8)) <- eval (extract (shl (expression.bv_nat 8 1) v_9) 0 8);
      store v_6 (bv_and v_7 (bv_xor v_10 (expression.bv_nat 8 255))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_7 v_9) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r64_1);
      let v_3 <- eval (sext (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 63)) 64);
      let (v_4 : expression (bv 64)) <- eval (extract (shl (expression.bv_nat 64 1) v_3) 0 64);
      setRegister (lhs.of_reg r64_1) (bv_and v_2 (bv_xor v_4 (expression.bv_nat 64 18446744073709551615)));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_2 v_3) 63);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- getRegister (lhs.of_reg r64_0);
      let (v_4 : expression (bv 61)) <- eval (extract v_3 0 61);
      let v_5 <- eval (concat (expression.bv_nat 3 0) v_4);
      let v_6 <- eval (add v_2 v_5);
      let v_7 <- load v_6 1;
      let (v_8 : expression (bv 3)) <- eval (extract v_3 61 64);
      let v_9 <- eval (concat (expression.bv_nat 5 0) v_8);
      let (v_10 : expression (bv 8)) <- eval (extract (shl (expression.bv_nat 8 1) v_9) 0 8);
      store v_6 (bv_and v_7 (bv_xor v_10 (expression.bv_nat 8 255))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_7 v_9) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r64_1);
      let v_3 <- getRegister (lhs.of_reg r64_0);
      let v_4 <- eval (bv_and v_3 (expression.bv_nat 64 63));
      let (v_5 : expression (bv 64)) <- eval (extract (shl (expression.bv_nat 64 1) v_4) 0 64);
      setRegister (lhs.of_reg r64_1) (bv_and v_2 (bv_xor v_5 (expression.bv_nat 64 18446744073709551615)));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_2 v_4) 63);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
     action
