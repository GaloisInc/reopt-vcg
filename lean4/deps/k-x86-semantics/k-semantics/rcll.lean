def rcll1 : instruction :=
  definst "rcll" $ do
    pattern fun cl (v_3310 : reg (bv 32)) => do
      v_9119 <- getRegister cf;
      v_9122 <- getRegister v_3310;
      v_9124 <- getRegister rcx;
      v_9128 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (extract v_9124 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_9130 <- eval (rolHelper (concat (mux (eq v_9119 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_9122) (uvalueMInt v_9128) 0);
      v_9131 <- eval (extract v_9130 0 1);
      v_9132 <- eval (extract v_9128 25 33);
      v_9133 <- eval (eq v_9132 (expression.bv_nat 8 1));
      v_9141 <- eval (eq v_9132 (expression.bv_nat 8 0));
      v_9144 <- getRegister of;
      setRegister (lhs.of_reg v_3310) (extract v_9130 1 33);
      setRegister of (mux (bit_or (bit_and v_9133 (notBool_ (eq (eq v_9131 (expression.bv_nat 1 1)) (eq (extract v_9130 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_9133) (bit_or (bit_and (notBool_ v_9141) undef) (bit_and v_9141 (eq v_9144 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_9131;
      pure ()
    pat_end;
    pattern fun (v_3313 : imm int) (v_3315 : reg (bv 32)) => do
      v_9155 <- getRegister cf;
      v_9158 <- getRegister v_3315;
      v_9163 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (handleImmediateWithSignExtend v_3313 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_9165 <- eval (rolHelper (concat (mux (eq v_9155 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_9158) (uvalueMInt v_9163) 0);
      v_9166 <- eval (extract v_9165 0 1);
      v_9167 <- eval (extract v_9163 25 33);
      v_9168 <- eval (eq v_9167 (expression.bv_nat 8 1));
      v_9176 <- eval (eq v_9167 (expression.bv_nat 8 0));
      v_9179 <- getRegister of;
      setRegister (lhs.of_reg v_3315) (extract v_9165 1 33);
      setRegister of (mux (bit_or (bit_and v_9168 (notBool_ (eq (eq v_9166 (expression.bv_nat 1 1)) (eq (extract v_9165 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_9168) (bit_or (bit_and (notBool_ v_9176) undef) (bit_and v_9176 (eq v_9179 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_9166;
      pure ()
    pat_end;
    pattern fun $0x1 (v_3319 : reg (bv 32)) => do
      v_9190 <- getRegister cf;
      v_9192 <- eval (mux (eq v_9190 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      v_9193 <- getRegister v_3319;
      v_9194 <- eval (concat v_9192 v_9193);
      v_9197 <- eval (add (bitwidthMInt v_9192) 32);
      v_9203 <- eval (add (extract (shl v_9194 1) 0 v_9197) (concat (mi (sub v_9197 1) 0) (extract v_9194 0 1)));
      v_9204 <- eval (extract v_9203 0 1);
      setRegister (lhs.of_reg v_3319) (extract v_9203 1 33);
      setRegister of (mux (notBool_ (eq (eq v_9204 (expression.bv_nat 1 1)) (eq (extract v_9203 1 2) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_9204;
      pure ()
    pat_end;
    pattern fun cl (v_3299 : Mem) => do
      v_15628 <- evaluateAddress v_3299;
      v_15629 <- getRegister cf;
      v_15632 <- load v_15628 4;
      v_15634 <- getRegister rcx;
      v_15638 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (extract v_15634 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_15640 <- eval (rolHelper (concat (mux (eq v_15629 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_15632) (uvalueMInt v_15638) 0);
      store v_15628 (extract v_15640 1 33) 4;
      v_15643 <- eval (extract v_15640 0 1);
      v_15644 <- eval (extract v_15638 25 33);
      v_15645 <- eval (eq v_15644 (expression.bv_nat 8 1));
      v_15653 <- eval (eq v_15644 (expression.bv_nat 8 0));
      v_15656 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_15645 (notBool_ (eq (eq v_15643 (expression.bv_nat 1 1)) (eq (extract v_15640 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_15645) (bit_or (bit_and (notBool_ v_15653) undef) (bit_and v_15653 (eq v_15656 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_15643;
      pure ()
    pat_end;
    pattern fun (v_3303 : imm int) (v_3302 : Mem) => do
      v_15665 <- evaluateAddress v_3302;
      v_15666 <- getRegister cf;
      v_15669 <- load v_15665 4;
      v_15674 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (handleImmediateWithSignExtend v_3303 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_15676 <- eval (rolHelper (concat (mux (eq v_15666 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_15669) (uvalueMInt v_15674) 0);
      store v_15665 (extract v_15676 1 33) 4;
      v_15679 <- eval (extract v_15676 0 1);
      v_15680 <- eval (extract v_15674 25 33);
      v_15681 <- eval (eq v_15680 (expression.bv_nat 8 1));
      v_15689 <- eval (eq v_15680 (expression.bv_nat 8 0));
      v_15692 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_15681 (notBool_ (eq (eq v_15679 (expression.bv_nat 1 1)) (eq (extract v_15676 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_15681) (bit_or (bit_and (notBool_ v_15689) undef) (bit_and v_15689 (eq v_15692 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_15679;
      pure ()
    pat_end
