def rcrb1 : instruction :=
  definst "rcrb" $ do
    pattern fun (_ : clReg) (v_2559 : reg (bv 8)) => do
      v_4318 <- getRegister rcx;
      v_4322 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (extract v_4318 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_4323 <- eval (extract v_4322 1 9);
      v_4325 <- getRegister cf;
      v_4327 <- getRegister v_2559;
      v_4329 <- eval (ror (concat (mux v_4325 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4327) v_4322);
      v_4335 <- getRegister of;
      setRegister (lhs.of_reg v_2559) (extract v_4329 1 9);
      setRegister cf (isBitSet v_4329 0);
      setRegister of (mux (eq v_4323 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_4329 1) (isBitSet v_4329 2))) (mux (eq v_4323 (expression.bv_nat 8 0)) v_4335 undef));
      pure ()
    pat_end;
    pattern fun (v_2560 : imm int) (v_2564 : reg (bv 8)) => do
      v_4346 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (handleImmediateWithSignExtend v_2560 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_4347 <- eval (extract v_4346 1 9);
      v_4349 <- getRegister cf;
      v_4351 <- getRegister v_2564;
      v_4353 <- eval (ror (concat (mux v_4349 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4351) v_4346);
      v_4359 <- getRegister of;
      setRegister (lhs.of_reg v_2564) (extract v_4353 1 9);
      setRegister cf (isBitSet v_4353 0);
      setRegister of (mux (eq v_4347 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_4353 1) (isBitSet v_4353 2))) (mux (eq v_4347 (expression.bv_nat 8 0)) v_4359 undef));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_2533 : Mem) => do
      v_11026 <- evaluateAddress v_2533;
      v_11027 <- getRegister cf;
      v_11029 <- load v_11026 1;
      v_11031 <- getRegister rcx;
      v_11035 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (extract v_11031 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_11036 <- eval (ror (concat (mux v_11027 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_11029) v_11035);
      store v_11026 (extract v_11036 1 9) 1;
      v_11039 <- eval (extract v_11035 1 9);
      v_11046 <- getRegister of;
      setRegister cf (isBitSet v_11036 0);
      setRegister of (mux (eq v_11039 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_11036 1) (isBitSet v_11036 2))) (mux (eq v_11039 (expression.bv_nat 8 0)) v_11046 undef));
      pure ()
    pat_end;
    pattern fun (v_2536 : imm int) (v_2537 : Mem) => do
      v_11052 <- evaluateAddress v_2537;
      v_11053 <- getRegister cf;
      v_11055 <- load v_11052 1;
      v_11060 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (handleImmediateWithSignExtend v_2536 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_11061 <- eval (ror (concat (mux v_11053 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_11055) v_11060);
      store v_11052 (extract v_11061 1 9) 1;
      v_11064 <- eval (extract v_11060 1 9);
      v_11071 <- getRegister of;
      setRegister cf (isBitSet v_11061 0);
      setRegister of (mux (eq v_11064 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_11061 1) (isBitSet v_11061 2))) (mux (eq v_11064 (expression.bv_nat 8 0)) v_11071 undef));
      pure ()
    pat_end
