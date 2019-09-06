def roll1 : instruction :=
  definst "roll" $ do
    pattern fun (_ : clReg) (v_2689 : reg (bv 32)) => do
      v_4720 <- getRegister rcx;
      v_4722 <- eval (bv_and (extract v_4720 56 64) (expression.bv_nat 8 31));
      v_4724 <- getRegister v_2689;
      v_4726 <- eval (rol v_4724 (concat (expression.bv_nat 24 0) v_4722));
      v_4728 <- eval (isBitSet v_4726 31);
      v_4731 <- eval (eq v_4722 (expression.bv_nat 8 0));
      v_4732 <- getRegister of;
      v_4735 <- getRegister cf;
      setRegister (lhs.of_reg v_2689) v_4726;
      setRegister cf (mux v_4731 v_4735 v_4728);
      setRegister of (mux (eq v_4722 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_4726 0) v_4728)) (mux v_4731 v_4732 undef));
      pure ()
    pat_end;
    pattern fun (v_2691 : imm int) (v_2694 : reg (bv 32)) => do
      v_4741 <- eval (bv_and (handleImmediateWithSignExtend v_2691 8 8) (expression.bv_nat 8 31));
      v_4743 <- getRegister v_2694;
      v_4745 <- eval (rol v_4743 (concat (expression.bv_nat 24 0) v_4741));
      v_4747 <- eval (isBitSet v_4745 31);
      v_4750 <- eval (eq v_4741 (expression.bv_nat 8 0));
      v_4751 <- getRegister of;
      v_4754 <- getRegister cf;
      setRegister (lhs.of_reg v_2694) v_4745;
      setRegister cf (mux v_4750 v_4754 v_4747);
      setRegister of (mux (eq v_4741 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_4745 0) v_4747)) (mux v_4750 v_4751 undef));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_2674 : Mem) => do
      v_11409 <- evaluateAddress v_2674;
      v_11410 <- load v_11409 4;
      v_11411 <- getRegister rcx;
      v_11413 <- eval (bv_and (extract v_11411 56 64) (expression.bv_nat 8 31));
      v_11415 <- eval (rol v_11410 (concat (expression.bv_nat 24 0) v_11413));
      store v_11409 v_11415 4;
      v_11419 <- eval (isBitSet v_11415 31);
      v_11422 <- eval (eq v_11413 (expression.bv_nat 8 0));
      v_11423 <- getRegister of;
      v_11426 <- getRegister cf;
      setRegister cf (mux v_11422 v_11426 v_11419);
      setRegister of (mux (eq v_11413 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_11415 0) v_11419)) (mux v_11422 v_11423 undef));
      pure ()
    pat_end;
    pattern fun (v_2677 : imm int) (v_2678 : Mem) => do
      v_11430 <- evaluateAddress v_2678;
      v_11431 <- load v_11430 4;
      v_11433 <- eval (bv_and (handleImmediateWithSignExtend v_2677 8 8) (expression.bv_nat 8 31));
      v_11435 <- eval (rol v_11431 (concat (expression.bv_nat 24 0) v_11433));
      store v_11430 v_11435 4;
      v_11439 <- eval (isBitSet v_11435 31);
      v_11442 <- eval (eq v_11433 (expression.bv_nat 8 0));
      v_11443 <- getRegister of;
      v_11446 <- getRegister cf;
      setRegister cf (mux v_11442 v_11446 v_11439);
      setRegister of (mux (eq v_11433 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_11435 0) v_11439)) (mux v_11442 v_11443 undef));
      pure ()
    pat_end;
    pattern fun (v_2683 : Mem) => do
      v_13105 <- evaluateAddress v_2683;
      v_13106 <- load v_13105 4;
      v_13107 <- eval (rol v_13106 (expression.bv_nat 32 1));
      store v_13105 v_13107 4;
      v_13110 <- eval (isBitSet v_13107 31);
      setRegister cf v_13110;
      setRegister of (notBool_ (eq (isBitSet v_13107 0) v_13110));
      pure ()
    pat_end
