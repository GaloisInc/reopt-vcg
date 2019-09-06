def rclb1 : instruction :=
  definst "rclb" $ do
    pattern fun (_ : clReg) (v_3363 : reg (bv 8)) => do
      v_8938 <- getRegister rcx;
      v_8942 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (extract v_8938 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_8943 <- eval (extract v_8942 1 9);
      v_8945 <- getRegister cf;
      v_8947 <- getRegister v_3363;
      v_8949 <- eval (rol (concat (mux v_8945 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_8947) v_8942);
      v_8950 <- eval (isBitSet v_8949 0);
      v_8955 <- getRegister of;
      setRegister (lhs.of_reg v_3363) (extract v_8949 1 9);
      setRegister cf v_8950;
      setRegister of (mux (eq v_8943 (expression.bv_nat 8 1)) (notBool_ (eq v_8950 (isBitSet v_8949 1))) (mux (eq v_8943 (expression.bv_nat 8 0)) v_8955 undef));
      pure ()
    pat_end;
    pattern fun (v_3367 : imm int) (v_3368 : reg (bv 8)) => do
      v_8965 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (handleImmediateWithSignExtend v_3367 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_8966 <- eval (extract v_8965 1 9);
      v_8968 <- getRegister cf;
      v_8970 <- getRegister v_3368;
      v_8972 <- eval (rol (concat (mux v_8968 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_8970) v_8965);
      v_8973 <- eval (isBitSet v_8972 0);
      v_8978 <- getRegister of;
      setRegister (lhs.of_reg v_3368) (extract v_8972 1 9);
      setRegister cf v_8973;
      setRegister of (mux (eq v_8966 (expression.bv_nat 8 1)) (notBool_ (eq v_8973 (isBitSet v_8972 1))) (mux (eq v_8966 (expression.bv_nat 8 0)) v_8978 undef));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_3340 : Mem) => do
      v_15272 <- evaluateAddress v_3340;
      v_15273 <- getRegister cf;
      v_15275 <- load v_15272 1;
      v_15277 <- getRegister rcx;
      v_15281 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (extract v_15277 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_15282 <- eval (rol (concat (mux v_15273 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_15275) v_15281);
      store v_15272 (extract v_15282 1 9) 1;
      v_15285 <- eval (extract v_15281 1 9);
      v_15287 <- eval (isBitSet v_15282 0);
      v_15292 <- getRegister of;
      setRegister cf v_15287;
      setRegister of (mux (eq v_15285 (expression.bv_nat 8 1)) (notBool_ (eq v_15287 (isBitSet v_15282 1))) (mux (eq v_15285 (expression.bv_nat 8 0)) v_15292 undef));
      pure ()
    pat_end;
    pattern fun (v_3344 : imm int) (v_3343 : Mem) => do
      v_15297 <- evaluateAddress v_3343;
      v_15298 <- getRegister cf;
      v_15300 <- load v_15297 1;
      v_15305 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (handleImmediateWithSignExtend v_3344 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_15306 <- eval (rol (concat (mux v_15298 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_15300) v_15305);
      store v_15297 (extract v_15306 1 9) 1;
      v_15309 <- eval (extract v_15305 1 9);
      v_15311 <- eval (isBitSet v_15306 0);
      v_15316 <- getRegister of;
      setRegister cf v_15311;
      setRegister of (mux (eq v_15309 (expression.bv_nat 8 1)) (notBool_ (eq v_15311 (isBitSet v_15306 1))) (mux (eq v_15309 (expression.bv_nat 8 0)) v_15316 undef));
      pure ()
    pat_end
