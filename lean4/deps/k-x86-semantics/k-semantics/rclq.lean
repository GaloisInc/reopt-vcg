def rclq1 : instruction :=
  definst "rclq" $ do
    pattern fun (_ : clReg) (v_2479 : reg (bv 64)) => do
      v_4077 <- getRegister rcx;
      v_4081 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (extract v_4077 56 64) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_4082 <- eval (extract v_4081 57 65);
      v_4084 <- getRegister cf;
      v_4086 <- getRegister v_2479;
      v_4088 <- eval (rol (concat (mux v_4084 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4086) v_4081);
      v_4089 <- eval (isBitSet v_4088 0);
      v_4094 <- getRegister of;
      setRegister (lhs.of_reg v_2479) (extract v_4088 1 65);
      setRegister cf v_4089;
      setRegister of (mux (eq v_4082 (expression.bv_nat 8 1)) (notBool_ (eq v_4089 (isBitSet v_4088 1))) (mux (eq v_4082 (expression.bv_nat 8 0)) v_4094 undef));
      pure ()
    pat_end;
    pattern fun (v_2484 : imm int) (v_2483 : reg (bv 64)) => do
      v_4104 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (handleImmediateWithSignExtend v_2484 8 8) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_4105 <- eval (extract v_4104 57 65);
      v_4107 <- getRegister cf;
      v_4109 <- getRegister v_2483;
      v_4111 <- eval (rol (concat (mux v_4107 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4109) v_4104);
      v_4112 <- eval (isBitSet v_4111 0);
      v_4117 <- getRegister of;
      setRegister (lhs.of_reg v_2483) (extract v_4111 1 65);
      setRegister cf v_4112;
      setRegister of (mux (eq v_4105 (expression.bv_nat 8 1)) (notBool_ (eq v_4112 (isBitSet v_4111 1))) (mux (eq v_4105 (expression.bv_nat 8 0)) v_4117 undef));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_2469 : Mem) => do
      v_10872 <- evaluateAddress v_2469;
      v_10873 <- getRegister cf;
      v_10875 <- load v_10872 8;
      v_10877 <- getRegister rcx;
      v_10881 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (extract v_10877 56 64) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_10882 <- eval (rol (concat (mux v_10873 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_10875) v_10881);
      store v_10872 (extract v_10882 1 65) 8;
      v_10885 <- eval (extract v_10881 57 65);
      v_10887 <- eval (isBitSet v_10882 0);
      v_10892 <- getRegister of;
      setRegister cf v_10887;
      setRegister of (mux (eq v_10885 (expression.bv_nat 8 1)) (notBool_ (eq v_10887 (isBitSet v_10882 1))) (mux (eq v_10885 (expression.bv_nat 8 0)) v_10892 undef));
      pure ()
    pat_end;
    pattern fun (v_2472 : imm int) (v_2473 : Mem) => do
      v_10897 <- evaluateAddress v_2473;
      v_10898 <- getRegister cf;
      v_10900 <- load v_10897 8;
      v_10905 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (handleImmediateWithSignExtend v_2472 8 8) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_10906 <- eval (rol (concat (mux v_10898 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_10900) v_10905);
      store v_10897 (extract v_10906 1 65) 8;
      v_10909 <- eval (extract v_10905 57 65);
      v_10911 <- eval (isBitSet v_10906 0);
      v_10916 <- getRegister of;
      setRegister cf v_10911;
      setRegister of (mux (eq v_10909 (expression.bv_nat 8 1)) (notBool_ (eq v_10911 (isBitSet v_10906 1))) (mux (eq v_10909 (expression.bv_nat 8 0)) v_10916 undef));
      pure ()
    pat_end
