def rclb1 : instruction :=
  definst "rclb" $ do
    pattern fun cl (v_3272 : reg (bv 8)) => do
      v_8917 <- getRegister cf;
      v_8920 <- getRegister v_3272;
      v_8922 <- getRegister rcx;
      v_8926 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (extract v_8922 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_8928 <- eval (rolHelper (concat (mux (eq v_8917 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_8920) (uvalueMInt v_8926) 0);
      v_8929 <- eval (extract v_8928 0 1);
      v_8930 <- eval (extract v_8926 1 9);
      v_8931 <- eval (eq v_8930 (expression.bv_nat 8 1));
      v_8939 <- eval (eq v_8930 (expression.bv_nat 8 0));
      v_8942 <- getRegister of;
      setRegister (lhs.of_reg v_3272) (extract v_8928 1 9);
      setRegister of (mux (bit_or (bit_and v_8931 (notBool_ (eq (eq v_8929 (expression.bv_nat 1 1)) (eq (extract v_8928 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_8931) (bit_or (bit_and (notBool_ v_8939) undef) (bit_and v_8939 (eq v_8942 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_8929;
      pure ()
    pat_end;
    pattern fun (v_3278 : imm int) (v_3276 : reg (bv 8)) => do
      v_8953 <- getRegister cf;
      v_8956 <- getRegister v_3276;
      v_8961 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (handleImmediateWithSignExtend v_3278 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_8963 <- eval (rolHelper (concat (mux (eq v_8953 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_8956) (uvalueMInt v_8961) 0);
      v_8964 <- eval (extract v_8963 0 1);
      v_8965 <- eval (extract v_8961 1 9);
      v_8966 <- eval (eq v_8965 (expression.bv_nat 8 1));
      v_8974 <- eval (eq v_8965 (expression.bv_nat 8 0));
      v_8977 <- getRegister of;
      setRegister (lhs.of_reg v_3276) (extract v_8963 1 9);
      setRegister of (mux (bit_or (bit_and v_8966 (notBool_ (eq (eq v_8964 (expression.bv_nat 1 1)) (eq (extract v_8963 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_8966) (bit_or (bit_and (notBool_ v_8974) undef) (bit_and v_8974 (eq v_8977 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_8964;
      pure ()
    pat_end;
    pattern fun $0x1 (v_3281 : reg (bv 8)) => do
      v_8988 <- getRegister cf;
      v_8990 <- eval (mux (eq v_8988 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      v_8991 <- getRegister v_3281;
      v_8992 <- eval (concat v_8990 v_8991);
      v_8995 <- eval (add (bitwidthMInt v_8990) 8);
      v_9001 <- eval (add (extract (shl v_8992 1) 0 v_8995) (concat (mi (sub v_8995 1) 0) (extract v_8992 0 1)));
      v_9002 <- eval (extract v_9001 0 1);
      setRegister (lhs.of_reg v_3281) (extract v_9001 1 9);
      setRegister of (mux (notBool_ (eq (eq v_9002 (expression.bv_nat 1 1)) (eq (extract v_9001 1 2) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_9002;
      pure ()
    pat_end;
    pattern fun cl (v_3263 : Mem) => do
      v_15503 <- evaluateAddress v_3263;
      v_15504 <- getRegister cf;
      v_15507 <- load v_15503 1;
      v_15509 <- getRegister rcx;
      v_15513 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (extract v_15509 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_15515 <- eval (rolHelper (concat (mux (eq v_15504 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_15507) (uvalueMInt v_15513) 0);
      store v_15503 (extract v_15515 1 9) 1;
      v_15518 <- eval (extract v_15515 0 1);
      v_15519 <- eval (extract v_15513 1 9);
      v_15520 <- eval (eq v_15519 (expression.bv_nat 8 1));
      v_15528 <- eval (eq v_15519 (expression.bv_nat 8 0));
      v_15531 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_15520 (notBool_ (eq (eq v_15518 (expression.bv_nat 1 1)) (eq (extract v_15515 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_15520) (bit_or (bit_and (notBool_ v_15528) undef) (bit_and v_15528 (eq v_15531 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_15518;
      pure ()
    pat_end;
    pattern fun (v_3267 : imm int) (v_3266 : Mem) => do
      v_15540 <- evaluateAddress v_3266;
      v_15541 <- getRegister cf;
      v_15544 <- load v_15540 1;
      v_15549 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (handleImmediateWithSignExtend v_3267 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_15551 <- eval (rolHelper (concat (mux (eq v_15541 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_15544) (uvalueMInt v_15549) 0);
      store v_15540 (extract v_15551 1 9) 1;
      v_15554 <- eval (extract v_15551 0 1);
      v_15555 <- eval (extract v_15549 1 9);
      v_15556 <- eval (eq v_15555 (expression.bv_nat 8 1));
      v_15564 <- eval (eq v_15555 (expression.bv_nat 8 0));
      v_15567 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_15556 (notBool_ (eq (eq v_15554 (expression.bv_nat 1 1)) (eq (extract v_15551 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_15556) (bit_or (bit_and (notBool_ v_15564) undef) (bit_and v_15564 (eq v_15567 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_15554;
      pure ()
    pat_end
