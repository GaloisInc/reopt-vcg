def rclw1 : instruction :=
  definst "rclw" $ do
    pattern fun (_ : clReg) (v_2504 : reg (bv 16)) => do
      v_4147 <- getRegister rcx;
      v_4151 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (extract v_4147 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_4152 <- eval (extract v_4151 9 17);
      v_4154 <- getRegister cf;
      v_4156 <- getRegister v_2504;
      v_4158 <- eval (rol (concat (mux v_4154 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4156) v_4151);
      v_4159 <- eval (isBitSet v_4158 0);
      v_4164 <- getRegister of;
      setRegister (lhs.of_reg v_2504) (extract v_4158 1 17);
      setRegister cf v_4159;
      setRegister of (mux (eq v_4152 (expression.bv_nat 8 1)) (notBool_ (eq v_4159 (isBitSet v_4158 1))) (mux (eq v_4152 (expression.bv_nat 8 0)) v_4164 undef));
      pure ()
    pat_end;
    pattern fun (v_2506 : imm int) (v_2509 : reg (bv 16)) => do
      v_4174 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (handleImmediateWithSignExtend v_2506 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_4175 <- eval (extract v_4174 9 17);
      v_4177 <- getRegister cf;
      v_4179 <- getRegister v_2509;
      v_4181 <- eval (rol (concat (mux v_4177 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4179) v_4174);
      v_4182 <- eval (isBitSet v_4181 0);
      v_4187 <- getRegister of;
      setRegister (lhs.of_reg v_2509) (extract v_4181 1 17);
      setRegister cf v_4182;
      setRegister of (mux (eq v_4175 (expression.bv_nat 8 1)) (notBool_ (eq v_4182 (isBitSet v_4181 1))) (mux (eq v_4175 (expression.bv_nat 8 0)) v_4187 undef));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_2492 : Mem) => do
      v_10949 <- evaluateAddress v_2492;
      v_10950 <- getRegister cf;
      v_10952 <- load v_10949 2;
      v_10954 <- getRegister rcx;
      v_10958 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (extract v_10954 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_10959 <- eval (rol (concat (mux v_10950 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_10952) v_10958);
      store v_10949 (extract v_10959 1 17) 2;
      v_10962 <- eval (extract v_10958 9 17);
      v_10964 <- eval (isBitSet v_10959 0);
      v_10969 <- getRegister of;
      setRegister cf v_10964;
      setRegister of (mux (eq v_10962 (expression.bv_nat 8 1)) (notBool_ (eq v_10964 (isBitSet v_10959 1))) (mux (eq v_10962 (expression.bv_nat 8 0)) v_10969 undef));
      pure ()
    pat_end;
    pattern fun (v_2495 : imm int) (v_2496 : Mem) => do
      v_10974 <- evaluateAddress v_2496;
      v_10975 <- getRegister cf;
      v_10977 <- load v_10974 2;
      v_10982 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (handleImmediateWithSignExtend v_2495 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_10983 <- eval (rol (concat (mux v_10975 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_10977) v_10982);
      store v_10974 (extract v_10983 1 17) 2;
      v_10986 <- eval (extract v_10982 9 17);
      v_10988 <- eval (isBitSet v_10983 0);
      v_10993 <- getRegister of;
      setRegister cf v_10988;
      setRegister of (mux (eq v_10986 (expression.bv_nat 8 1)) (notBool_ (eq v_10988 (isBitSet v_10983 1))) (mux (eq v_10986 (expression.bv_nat 8 0)) v_10993 undef));
      pure ()
    pat_end
