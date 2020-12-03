def rclq : instruction :=
  definst "rclq" $ do
    instr_pat $ fun (_ : clReg) (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- getRegister cf;
      let v_3 <- load v_1 8;
      let v_4 <- eval (concat (mux v_2 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_3);
      let v_5 <- getRegister rcx;
      let (v_6 : expression (bv 8)) <- eval (extract v_5 56 64);
      let v_7 <- eval (concat (expression.bv_nat 57 0) (bv_and v_6 (expression.bv_nat 8 63)));
      let v_8 <- eval (urem v_7 (expression.bv_nat 65 65));
      let v_9 <- eval (rol v_4 v_8);
      let (v_10 : expression (bv 64)) <- eval (extract v_9 1 65);
      store v_1 v_10 8;
      let (v_12 : expression (bv 8)) <- eval (extract v_8 57 65);
      let v_13 <- eval (isBitSet v_9 0);
      let v_14 <- getRegister of;
      setRegister cf v_13;
      setRegister of (mux (eq v_12 (expression.bv_nat 8 1)) (notBool_ (eq v_13 (isBitSet v_9 1))) (mux (eq v_12 (expression.bv_nat 8 0)) v_14 undef));
      pure ()
     action;
    instr_pat $ fun (_ : clReg) (r64_0 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister rcx;
      let (v_2 : expression (bv 8)) <- eval (extract v_1 56 64);
      let v_3 <- eval (concat (expression.bv_nat 57 0) (bv_and v_2 (expression.bv_nat 8 63)));
      let v_4 <- eval (urem v_3 (expression.bv_nat 65 65));
      let (v_5 : expression (bv 8)) <- eval (extract v_4 57 65);
      let v_6 <- getRegister cf;
      let v_7 <- getRegister (lhs.of_reg r64_0);
      let v_8 <- eval (concat (mux v_6 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_7);
      let v_9 <- eval (rol v_8 v_4);
      let v_10 <- eval (isBitSet v_9 0);
      let v_11 <- getRegister of;
      let (v_12 : expression (bv 64)) <- eval (extract v_9 1 65);
      setRegister (lhs.of_reg r64_0) v_12;
      setRegister cf v_10;
      setRegister of (mux (eq v_5 (expression.bv_nat 8 1)) (notBool_ (eq v_10 (isBitSet v_9 1))) (mux (eq v_5 (expression.bv_nat 8 0)) v_11 undef));
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- getRegister cf;
      let v_4 <- load v_2 8;
      let v_5 <- eval (concat (mux v_3 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4);
      let v_6 <- eval (concat (expression.bv_nat 57 0) (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 63)));
      let v_7 <- eval (urem v_6 (expression.bv_nat 65 65));
      let v_8 <- eval (rol v_5 v_7);
      let (v_9 : expression (bv 64)) <- eval (extract v_8 1 65);
      store v_2 v_9 8;
      let (v_11 : expression (bv 8)) <- eval (extract v_7 57 65);
      let v_12 <- eval (isBitSet v_8 0);
      let v_13 <- getRegister of;
      setRegister cf v_12;
      setRegister of (mux (eq v_11 (expression.bv_nat 8 1)) (notBool_ (eq v_12 (isBitSet v_8 1))) (mux (eq v_11 (expression.bv_nat 8 0)) v_13 undef));
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- eval (concat (expression.bv_nat 57 0) (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 63)));
      let v_3 <- eval (urem v_2 (expression.bv_nat 65 65));
      let (v_4 : expression (bv 8)) <- eval (extract v_3 57 65);
      let v_5 <- getRegister cf;
      let v_6 <- getRegister (lhs.of_reg r64_1);
      let v_7 <- eval (concat (mux v_5 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_6);
      let v_8 <- eval (rol v_7 v_3);
      let v_9 <- eval (isBitSet v_8 0);
      let v_10 <- getRegister of;
      let (v_11 : expression (bv 64)) <- eval (extract v_8 1 65);
      setRegister (lhs.of_reg r64_1) v_11;
      setRegister cf v_9;
      setRegister of (mux (eq v_4 (expression.bv_nat 8 1)) (notBool_ (eq v_9 (isBitSet v_8 1))) (mux (eq v_4 (expression.bv_nat 8 0)) v_10 undef));
      pure ()
     action
