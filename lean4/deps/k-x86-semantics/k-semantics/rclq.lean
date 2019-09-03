def rclq1 : instruction :=
  definst "rclq" $ do
    pattern fun cl (v_2402 : reg (bv 64)) => do
      v_3999 <- getRegister cf;
      v_4002 <- getRegister v_2402;
      v_4004 <- getRegister rcx;
      v_4008 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (extract v_4004 56 64) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_4010 <- eval (rolHelper (concat (mux (eq v_3999 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4002) (uvalueMInt v_4008) 0);
      v_4011 <- eval (extract v_4010 0 1);
      v_4012 <- eval (extract v_4008 57 65);
      v_4013 <- eval (eq v_4012 (expression.bv_nat 8 1));
      v_4021 <- eval (eq v_4012 (expression.bv_nat 8 0));
      v_4024 <- getRegister of;
      setRegister (lhs.of_reg v_2402) (extract v_4010 1 65);
      setRegister of (mux (bit_or (bit_and v_4013 (notBool_ (eq (eq v_4011 (expression.bv_nat 1 1)) (eq (extract v_4010 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_4013) (bit_or (bit_and (notBool_ v_4021) undef) (bit_and v_4021 (eq v_4024 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_4011;
      pure ()
    pat_end;
    pattern fun (v_2405 : imm int) (v_2407 : reg (bv 64)) => do
      v_4035 <- getRegister cf;
      v_4038 <- getRegister v_2407;
      v_4043 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (handleImmediateWithSignExtend v_2405 8 8) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_4045 <- eval (rolHelper (concat (mux (eq v_4035 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4038) (uvalueMInt v_4043) 0);
      v_4046 <- eval (extract v_4045 0 1);
      v_4047 <- eval (extract v_4043 57 65);
      v_4048 <- eval (eq v_4047 (expression.bv_nat 8 1));
      v_4056 <- eval (eq v_4047 (expression.bv_nat 8 0));
      v_4059 <- getRegister of;
      setRegister (lhs.of_reg v_2407) (extract v_4045 1 65);
      setRegister of (mux (bit_or (bit_and v_4048 (notBool_ (eq (eq v_4046 (expression.bv_nat 1 1)) (eq (extract v_4045 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_4048) (bit_or (bit_and (notBool_ v_4056) undef) (bit_and v_4056 (eq v_4059 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_4046;
      pure ()
    pat_end;
    pattern fun $0x1 (v_2411 : reg (bv 64)) => do
      v_4070 <- getRegister cf;
      v_4072 <- eval (mux (eq v_4070 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      v_4073 <- getRegister v_2411;
      v_4074 <- eval (concat v_4072 v_4073);
      v_4077 <- eval (add (bitwidthMInt v_4072) 64);
      v_4083 <- eval (add (extract (shl v_4074 1) 0 v_4077) (concat (mi (sub v_4077 1) 0) (extract v_4074 0 1)));
      v_4084 <- eval (extract v_4083 0 1);
      setRegister (lhs.of_reg v_2411) (extract v_4083 1 65);
      setRegister of (mux (notBool_ (eq (eq v_4084 (expression.bv_nat 1 1)) (eq (extract v_4083 1 2) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_4084;
      pure ()
    pat_end;
    pattern fun cl (v_2391 : Mem) => do
      v_13333 <- evaluateAddress v_2391;
      v_13334 <- getRegister cf;
      v_13337 <- load v_13333 8;
      v_13339 <- getRegister rcx;
      v_13343 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (extract v_13339 56 64) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_13345 <- eval (rolHelper (concat (mux (eq v_13334 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_13337) (uvalueMInt v_13343) 0);
      store v_13333 (extract v_13345 1 65) 8;
      v_13348 <- eval (extract v_13345 0 1);
      v_13349 <- eval (extract v_13343 57 65);
      v_13350 <- eval (eq v_13349 (expression.bv_nat 8 1));
      v_13358 <- eval (eq v_13349 (expression.bv_nat 8 0));
      v_13361 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_13350 (notBool_ (eq (eq v_13348 (expression.bv_nat 1 1)) (eq (extract v_13345 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_13350) (bit_or (bit_and (notBool_ v_13358) undef) (bit_and v_13358 (eq v_13361 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_13348;
      pure ()
    pat_end;
    pattern fun (v_2395 : imm int) (v_2394 : Mem) => do
      v_13370 <- evaluateAddress v_2394;
      v_13371 <- getRegister cf;
      v_13374 <- load v_13370 8;
      v_13379 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (handleImmediateWithSignExtend v_2395 8 8) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_13381 <- eval (rolHelper (concat (mux (eq v_13371 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_13374) (uvalueMInt v_13379) 0);
      store v_13370 (extract v_13381 1 65) 8;
      v_13384 <- eval (extract v_13381 0 1);
      v_13385 <- eval (extract v_13379 57 65);
      v_13386 <- eval (eq v_13385 (expression.bv_nat 8 1));
      v_13394 <- eval (eq v_13385 (expression.bv_nat 8 0));
      v_13397 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_13386 (notBool_ (eq (eq v_13384 (expression.bv_nat 1 1)) (eq (extract v_13381 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_13386) (bit_or (bit_and (notBool_ v_13394) undef) (bit_and v_13394 (eq v_13397 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_13384;
      pure ()
    pat_end
