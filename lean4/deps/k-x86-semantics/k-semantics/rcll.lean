def rcll1 : instruction :=
  definst "rcll" $ do
    pattern fun cl (v_3358 : reg (bv 32)) => do
      v_9015 <- getRegister rcx;
      v_9019 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (extract v_9015 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_9020 <- eval (extract v_9019 25 33);
      v_9021 <- eval (eq v_9020 (expression.bv_nat 8 1));
      v_9022 <- getRegister cf;
      v_9025 <- getRegister v_3358;
      v_9027 <- eval (rol (concat (mux (eq v_9022 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_9025) v_9019);
      v_9028 <- eval (isBitSet v_9027 0);
      v_9034 <- eval (eq v_9020 (expression.bv_nat 8 0));
      v_9037 <- getRegister of;
      setRegister (lhs.of_reg v_3358) (extract v_9027 1 33);
      setRegister cf v_9028;
      setRegister of (bit_or (bit_and v_9021 (notBool_ (eq v_9028 (isBitSet v_9027 1)))) (bit_and (notBool_ v_9021) (bit_or (bit_and (notBool_ v_9034) undef) (bit_and v_9034 (eq v_9037 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_3363 : imm int) (v_3362 : reg (bv 32)) => do
      v_9050 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (handleImmediateWithSignExtend v_3363 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_9051 <- eval (extract v_9050 25 33);
      v_9052 <- eval (eq v_9051 (expression.bv_nat 8 1));
      v_9053 <- getRegister cf;
      v_9056 <- getRegister v_3362;
      v_9058 <- eval (rol (concat (mux (eq v_9053 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_9056) v_9050);
      v_9059 <- eval (isBitSet v_9058 0);
      v_9065 <- eval (eq v_9051 (expression.bv_nat 8 0));
      v_9068 <- getRegister of;
      setRegister (lhs.of_reg v_3362) (extract v_9058 1 33);
      setRegister cf v_9059;
      setRegister of (bit_or (bit_and v_9052 (notBool_ (eq v_9059 (isBitSet v_9058 1)))) (bit_and (notBool_ v_9052) (bit_or (bit_and (notBool_ v_9065) undef) (bit_and v_9065 (eq v_9068 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun cl (v_3348 : Mem) => do
      v_15391 <- evaluateAddress v_3348;
      v_15392 <- getRegister cf;
      v_15395 <- load v_15391 4;
      v_15397 <- getRegister rcx;
      v_15401 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (extract v_15397 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_15402 <- eval (rol (concat (mux (eq v_15392 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_15395) v_15401);
      store v_15391 (extract v_15402 1 33) 4;
      v_15405 <- eval (extract v_15401 25 33);
      v_15406 <- eval (eq v_15405 (expression.bv_nat 8 1));
      v_15407 <- eval (isBitSet v_15402 0);
      v_15413 <- eval (eq v_15405 (expression.bv_nat 8 0));
      v_15416 <- getRegister of;
      setRegister cf v_15407;
      setRegister of (bit_or (bit_and v_15406 (notBool_ (eq v_15407 (isBitSet v_15402 1)))) (bit_and (notBool_ v_15406) (bit_or (bit_and (notBool_ v_15413) undef) (bit_and v_15413 (eq v_15416 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_3351 : imm int) (v_3352 : Mem) => do
      v_15424 <- evaluateAddress v_3352;
      v_15425 <- getRegister cf;
      v_15428 <- load v_15424 4;
      v_15433 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (handleImmediateWithSignExtend v_3351 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_15434 <- eval (rol (concat (mux (eq v_15425 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_15428) v_15433);
      store v_15424 (extract v_15434 1 33) 4;
      v_15437 <- eval (extract v_15433 25 33);
      v_15438 <- eval (eq v_15437 (expression.bv_nat 8 1));
      v_15439 <- eval (isBitSet v_15434 0);
      v_15445 <- eval (eq v_15437 (expression.bv_nat 8 0));
      v_15448 <- getRegister of;
      setRegister cf v_15439;
      setRegister of (bit_or (bit_and v_15438 (notBool_ (eq v_15439 (isBitSet v_15434 1)))) (bit_and (notBool_ v_15438) (bit_or (bit_and (notBool_ v_15445) undef) (bit_and v_15445 (eq v_15448 (expression.bv_nat 1 1))))));
      pure ()
    pat_end
