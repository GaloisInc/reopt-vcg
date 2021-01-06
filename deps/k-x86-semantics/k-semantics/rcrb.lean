def rcrb : instruction :=
  definst "rcrb" $ do
    instr_pat $ fun (_ : clReg) (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- getRegister cf;
      let v_3 <- load v_1 1;
      let v_4 <- eval (concat (mux v_2 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_3);
      let v_5 <- getRegister rcx;
      let (v_6 : expression (bv 8)) <- eval (extract v_5 56 64);
      let v_7 <- eval (concat (expression.bv_nat 1 0) (bv_and v_6 (expression.bv_nat 8 31)));
      let v_8 <- eval (urem v_7 (expression.bv_nat 9 9));
      let v_9 <- eval (ror v_4 v_8);
      let (v_10 : expression (bv 8)) <- eval (extract v_9 1 9);
      store v_1 v_10 1;
      let (v_12 : expression (bv 8)) <- eval (extract v_8 1 9);
      let v_13 <- getRegister of;
      setRegister cf (isBitSet v_9 0);
      setRegister of (mux (eq v_12 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_9 1) (isBitSet v_9 2))) (mux (eq v_12 (expression.bv_nat 8 0)) v_13 undef));
      pure ()
     action;
    instr_pat $ fun (_ : clReg) (rh_0 : reg (bv 8)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister rcx;
      let (v_2 : expression (bv 8)) <- eval (extract v_1 56 64);
      let v_3 <- eval (concat (expression.bv_nat 1 0) (bv_and v_2 (expression.bv_nat 8 31)));
      let v_4 <- eval (urem v_3 (expression.bv_nat 9 9));
      let (v_5 : expression (bv 8)) <- eval (extract v_4 1 9);
      let v_6 <- getRegister cf;
      let v_7 <- getRegister (lhs.of_reg rh_0);
      let v_8 <- eval (concat (mux v_6 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_7);
      let v_9 <- eval (ror v_8 v_4);
      let v_10 <- getRegister of;
      let (v_11 : expression (bv 8)) <- eval (extract v_9 1 9);
      setRegister (lhs.of_reg rh_0) v_11;
      setRegister cf (isBitSet v_9 0);
      setRegister of (mux (eq v_5 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_9 1) (isBitSet v_9 2))) (mux (eq v_5 (expression.bv_nat 8 0)) v_10 undef));
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- getRegister cf;
      let v_4 <- load v_2 1;
      let v_5 <- eval (concat (mux v_3 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4);
      let v_6 <- eval (concat (expression.bv_nat 1 0) (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 31)));
      let v_7 <- eval (urem v_6 (expression.bv_nat 9 9));
      let v_8 <- eval (ror v_5 v_7);
      let (v_9 : expression (bv 8)) <- eval (extract v_8 1 9);
      store v_2 v_9 1;
      let (v_11 : expression (bv 8)) <- eval (extract v_7 1 9);
      let v_12 <- getRegister of;
      setRegister cf (isBitSet v_8 0);
      setRegister of (mux (eq v_11 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_8 1) (isBitSet v_8 2))) (mux (eq v_11 (expression.bv_nat 8 0)) v_12 undef));
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (rh_1 : reg (bv 8)) =>
     let action : semantics Unit := do
      let v_2 <- eval (concat (expression.bv_nat 1 0) (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 31)));
      let v_3 <- eval (urem v_2 (expression.bv_nat 9 9));
      let (v_4 : expression (bv 8)) <- eval (extract v_3 1 9);
      let v_5 <- getRegister cf;
      let v_6 <- getRegister (lhs.of_reg rh_1);
      let v_7 <- eval (concat (mux v_5 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_6);
      let v_8 <- eval (ror v_7 v_3);
      let v_9 <- getRegister of;
      let (v_10 : expression (bv 8)) <- eval (extract v_8 1 9);
      setRegister (lhs.of_reg rh_1) v_10;
      setRegister cf (isBitSet v_8 0);
      setRegister of (mux (eq v_4 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_8 1) (isBitSet v_8 2))) (mux (eq v_4 (expression.bv_nat 8 0)) v_9 undef));
      pure ()
     action
