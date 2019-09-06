def rcll1 : instruction :=
  definst "rcll" $ do
    pattern fun (_ : clReg) (v_3386 : reg (bv 32)) => do
      v_9008 <- getRegister rcx;
      v_9012 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (extract v_9008 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_9013 <- eval (extract v_9012 25 33);
      v_9015 <- getRegister cf;
      v_9017 <- getRegister v_3386;
      v_9019 <- eval (rol (concat (mux v_9015 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_9017) v_9012);
      v_9020 <- eval (isBitSet v_9019 0);
      v_9025 <- getRegister of;
      setRegister (lhs.of_reg v_3386) (extract v_9019 1 33);
      setRegister cf v_9020;
      setRegister of (mux (eq v_9013 (expression.bv_nat 8 1)) (notBool_ (eq v_9020 (isBitSet v_9019 1))) (mux (eq v_9013 (expression.bv_nat 8 0)) v_9025 undef));
      pure ()
    pat_end;
    pattern fun (v_3390 : imm int) (v_3391 : reg (bv 32)) => do
      v_9035 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (handleImmediateWithSignExtend v_3390 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_9036 <- eval (extract v_9035 25 33);
      v_9038 <- getRegister cf;
      v_9040 <- getRegister v_3391;
      v_9042 <- eval (rol (concat (mux v_9038 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_9040) v_9035);
      v_9043 <- eval (isBitSet v_9042 0);
      v_9048 <- getRegister of;
      setRegister (lhs.of_reg v_3391) (extract v_9042 1 33);
      setRegister cf v_9043;
      setRegister of (mux (eq v_9036 (expression.bv_nat 8 1)) (notBool_ (eq v_9043 (isBitSet v_9042 1))) (mux (eq v_9036 (expression.bv_nat 8 0)) v_9048 undef));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_3376 : Mem) => do
      v_15349 <- evaluateAddress v_3376;
      v_15350 <- getRegister cf;
      v_15352 <- load v_15349 4;
      v_15354 <- getRegister rcx;
      v_15358 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (extract v_15354 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_15359 <- eval (rol (concat (mux v_15350 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_15352) v_15358);
      store v_15349 (extract v_15359 1 33) 4;
      v_15362 <- eval (extract v_15358 25 33);
      v_15364 <- eval (isBitSet v_15359 0);
      v_15369 <- getRegister of;
      setRegister cf v_15364;
      setRegister of (mux (eq v_15362 (expression.bv_nat 8 1)) (notBool_ (eq v_15364 (isBitSet v_15359 1))) (mux (eq v_15362 (expression.bv_nat 8 0)) v_15369 undef));
      pure ()
    pat_end;
    pattern fun (v_3380 : imm int) (v_3379 : Mem) => do
      v_15374 <- evaluateAddress v_3379;
      v_15375 <- getRegister cf;
      v_15377 <- load v_15374 4;
      v_15382 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (handleImmediateWithSignExtend v_3380 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_15383 <- eval (rol (concat (mux v_15375 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_15377) v_15382);
      store v_15374 (extract v_15383 1 33) 4;
      v_15386 <- eval (extract v_15382 25 33);
      v_15388 <- eval (isBitSet v_15383 0);
      v_15393 <- getRegister of;
      setRegister cf v_15388;
      setRegister of (mux (eq v_15386 (expression.bv_nat 8 1)) (notBool_ (eq v_15388 (isBitSet v_15383 1))) (mux (eq v_15386 (expression.bv_nat 8 0)) v_15393 undef));
      pure ()
    pat_end
