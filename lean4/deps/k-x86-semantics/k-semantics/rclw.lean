def rclw1 : instruction :=
  definst "rclw" $ do
    pattern fun cl (v_2414 : reg (bv 16)) => do
      v_4091 <- getRegister cf;
      v_4094 <- getRegister v_2414;
      v_4096 <- getRegister rcx;
      v_4100 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (extract v_4096 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_4102 <- eval (rolHelper (concat (mux (eq v_4091 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4094) (uvalueMInt v_4100) 0);
      v_4103 <- eval (extract v_4102 0 1);
      v_4104 <- eval (extract v_4100 9 17);
      v_4105 <- eval (eq v_4104 (expression.bv_nat 8 1));
      v_4113 <- eval (eq v_4104 (expression.bv_nat 8 0));
      v_4116 <- getRegister of;
      setRegister (lhs.of_reg v_2414) (extract v_4102 1 17);
      setRegister of (mux (bit_or (bit_and v_4105 (notBool_ (eq (eq v_4103 (expression.bv_nat 1 1)) (eq (extract v_4102 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_4105) (bit_or (bit_and (notBool_ v_4113) undef) (bit_and v_4113 (eq v_4116 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_4103;
      pure ()
    pat_end;
    pattern fun (v_2415 : imm int) (v_2419 : reg (bv 16)) => do
      v_4127 <- getRegister cf;
      v_4130 <- getRegister v_2419;
      v_4135 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (handleImmediateWithSignExtend v_2415 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_4137 <- eval (rolHelper (concat (mux (eq v_4127 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4130) (uvalueMInt v_4135) 0);
      v_4138 <- eval (extract v_4137 0 1);
      v_4139 <- eval (extract v_4135 9 17);
      v_4140 <- eval (eq v_4139 (expression.bv_nat 8 1));
      v_4148 <- eval (eq v_4139 (expression.bv_nat 8 0));
      v_4151 <- getRegister of;
      setRegister (lhs.of_reg v_2419) (extract v_4137 1 17);
      setRegister of (mux (bit_or (bit_and v_4140 (notBool_ (eq (eq v_4138 (expression.bv_nat 1 1)) (eq (extract v_4137 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_4140) (bit_or (bit_and (notBool_ v_4148) undef) (bit_and v_4148 (eq v_4151 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_4138;
      pure ()
    pat_end;
    pattern fun $0x1 (v_2423 : reg (bv 16)) => do
      v_4162 <- getRegister cf;
      v_4165 <- getRegister v_2423;
      v_4166 <- eval (concat (mux (eq v_4162 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4165);
      v_4168 <- eval (bitwidthMInt v_4166);
      v_4174 <- eval (add (extract (shl v_4166 1) 0 v_4168) (concat (mi (sub v_4168 1) 0) (extract v_4166 0 1)));
      v_4175 <- eval (extract v_4174 0 1);
      setRegister (lhs.of_reg v_2423) (extract v_4174 1 17);
      setRegister of (mux (notBool_ (eq (eq v_4175 (expression.bv_nat 1 1)) (eq (extract v_4174 1 2) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_4175;
      pure ()
    pat_end;
    pattern fun cl (v_2401 : Mem) => do
      v_13554 <- evaluateAddress v_2401;
      v_13555 <- getRegister cf;
      v_13558 <- load v_13554 2;
      v_13560 <- getRegister rcx;
      v_13564 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (extract v_13560 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_13566 <- eval (rolHelper (concat (mux (eq v_13555 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_13558) (uvalueMInt v_13564) 0);
      store v_13554 (extract v_13566 1 17) 2;
      v_13569 <- eval (extract v_13566 0 1);
      v_13570 <- eval (extract v_13564 9 17);
      v_13571 <- eval (eq v_13570 (expression.bv_nat 8 1));
      v_13579 <- eval (eq v_13570 (expression.bv_nat 8 0));
      v_13582 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_13571 (notBool_ (eq (eq v_13569 (expression.bv_nat 1 1)) (eq (extract v_13566 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_13571) (bit_or (bit_and (notBool_ v_13579) undef) (bit_and v_13579 (eq v_13582 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_13569;
      pure ()
    pat_end;
    pattern fun (v_2404 : imm int) (v_2405 : Mem) => do
      v_13591 <- evaluateAddress v_2405;
      v_13592 <- getRegister cf;
      v_13595 <- load v_13591 2;
      v_13600 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (handleImmediateWithSignExtend v_2404 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_13602 <- eval (rolHelper (concat (mux (eq v_13592 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_13595) (uvalueMInt v_13600) 0);
      store v_13591 (extract v_13602 1 17) 2;
      v_13605 <- eval (extract v_13602 0 1);
      v_13606 <- eval (extract v_13600 9 17);
      v_13607 <- eval (eq v_13606 (expression.bv_nat 8 1));
      v_13615 <- eval (eq v_13606 (expression.bv_nat 8 0));
      v_13618 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_13607 (notBool_ (eq (eq v_13605 (expression.bv_nat 1 1)) (eq (extract v_13602 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_13607) (bit_or (bit_and (notBool_ v_13615) undef) (bit_and v_13615 (eq v_13618 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_13605;
      pure ()
    pat_end
