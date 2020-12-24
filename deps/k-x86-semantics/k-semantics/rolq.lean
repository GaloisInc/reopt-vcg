def rolq : instruction :=
  definst "rolq" $ do
    instr_pat $ fun (_ : clReg) (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- load v_1 8;
      let v_3 <- getRegister rcx;
      let (v_4 : expression (bv 8)) <- eval (extract v_3 56 64);
      let v_5 <- eval (bv_and v_4 (expression.bv_nat 8 63));
      let v_6 <- eval (concat (expression.bv_nat 56 0) v_5);
      let v_7 <- eval (rol v_2 v_6);
      store v_1 v_7 8;
      let v_9 <- eval (isBitSet v_7 63);
      let v_10 <- eval (eq v_5 (expression.bv_nat 8 0));
      let v_11 <- getRegister of;
      let v_12 <- getRegister cf;
      setRegister cf (mux v_10 v_12 v_9);
      setRegister of (mux (eq v_5 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_7 0) v_9)) (mux v_10 v_11 undef));
      pure ()
     action;
    instr_pat $ fun (_ : clReg) (r64_0 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister rcx;
      let (v_2 : expression (bv 8)) <- eval (extract v_1 56 64);
      let v_3 <- eval (bv_and v_2 (expression.bv_nat 8 63));
      let v_4 <- getRegister (lhs.of_reg r64_0);
      let v_5 <- eval (concat (expression.bv_nat 56 0) v_3);
      let v_6 <- eval (rol v_4 v_5);
      let v_7 <- eval (isBitSet v_6 63);
      let v_8 <- eval (eq v_3 (expression.bv_nat 8 0));
      let v_9 <- getRegister of;
      let v_10 <- getRegister cf;
      setRegister (lhs.of_reg r64_0) v_6;
      setRegister cf (mux v_8 v_10 v_7);
      setRegister of (mux (eq v_3 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_6 0) v_7)) (mux v_8 v_9 undef));
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- load v_2 8;
      let v_4 <- eval (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 63));
      let v_5 <- eval (concat (expression.bv_nat 56 0) v_4);
      let v_6 <- eval (rol v_3 v_5);
      store v_2 v_6 8;
      let v_8 <- eval (isBitSet v_6 63);
      let v_9 <- eval (eq v_4 (expression.bv_nat 8 0));
      let v_10 <- getRegister of;
      let v_11 <- getRegister cf;
      setRegister cf (mux v_9 v_11 v_8);
      setRegister of (mux (eq v_4 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_6 0) v_8)) (mux v_9 v_10 undef));
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- eval (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 63));
      let v_3 <- getRegister (lhs.of_reg r64_1);
      let v_4 <- eval (concat (expression.bv_nat 56 0) v_2);
      let v_5 <- eval (rol v_3 v_4);
      let v_6 <- eval (isBitSet v_5 63);
      let v_7 <- eval (eq v_2 (expression.bv_nat 8 0));
      let v_8 <- getRegister of;
      let v_9 <- getRegister cf;
      setRegister (lhs.of_reg r64_1) v_5;
      setRegister cf (mux v_7 v_9 v_6);
      setRegister of (mux (eq v_2 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_5 0) v_6)) (mux v_7 v_8 undef));
      pure ()
     action