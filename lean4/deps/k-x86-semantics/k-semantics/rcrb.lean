def rcrb1 : instruction :=
  definst "rcrb" $ do
    pattern fun cl (v_2532 : reg (bv 8)) => do
      v_4342 <- getRegister rcx;
      v_4346 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (extract v_4342 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_4347 <- eval (extract v_4346 1 9);
      v_4348 <- eval (eq v_4347 (expression.bv_nat 8 1));
      v_4349 <- getRegister cf;
      v_4352 <- getRegister v_2532;
      v_4354 <- eval (ror (concat (mux (eq v_4349 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4352) v_4346);
      v_4361 <- eval (eq v_4347 (expression.bv_nat 8 0));
      v_4364 <- getRegister of;
      setRegister (lhs.of_reg v_2532) (extract v_4354 1 9);
      setRegister cf (isBitSet v_4354 0);
      setRegister of (bit_or (bit_and v_4348 (notBool_ (eq (isBitSet v_4354 1) (isBitSet v_4354 2)))) (bit_and (notBool_ v_4348) (bit_or (bit_and (notBool_ v_4361) undef) (bit_and v_4361 (eq v_4364 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2535 : imm int) (v_2537 : reg (bv 8)) => do
      v_4378 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (handleImmediateWithSignExtend v_2535 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_4379 <- eval (extract v_4378 1 9);
      v_4380 <- eval (eq v_4379 (expression.bv_nat 8 1));
      v_4381 <- getRegister cf;
      v_4384 <- getRegister v_2537;
      v_4386 <- eval (ror (concat (mux (eq v_4381 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4384) v_4378);
      v_4393 <- eval (eq v_4379 (expression.bv_nat 8 0));
      v_4396 <- getRegister of;
      setRegister (lhs.of_reg v_2537) (extract v_4386 1 9);
      setRegister cf (isBitSet v_4386 0);
      setRegister of (bit_or (bit_and v_4380 (notBool_ (eq (isBitSet v_4386 1) (isBitSet v_4386 2)))) (bit_and (notBool_ v_4380) (bit_or (bit_and (notBool_ v_4393) undef) (bit_and v_4393 (eq v_4396 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun cl (v_2508 : Mem) => do
      v_11816 <- evaluateAddress v_2508;
      v_11817 <- getRegister cf;
      v_11820 <- load v_11816 1;
      v_11822 <- getRegister rcx;
      v_11826 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (extract v_11822 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_11827 <- eval (ror (concat (mux (eq v_11817 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_11820) v_11826);
      store v_11816 (extract v_11827 1 9) 1;
      v_11830 <- eval (extract v_11826 1 9);
      v_11831 <- eval (eq v_11830 (expression.bv_nat 8 1));
      v_11838 <- eval (eq v_11830 (expression.bv_nat 8 0));
      v_11841 <- getRegister of;
      setRegister cf (isBitSet v_11827 0);
      setRegister of (bit_or (bit_and v_11831 (notBool_ (eq (isBitSet v_11827 1) (isBitSet v_11827 2)))) (bit_and (notBool_ v_11831) (bit_or (bit_and (notBool_ v_11838) undef) (bit_and v_11838 (eq v_11841 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2511 : imm int) (v_2512 : Mem) => do
      v_11850 <- evaluateAddress v_2512;
      v_11851 <- getRegister cf;
      v_11854 <- load v_11850 1;
      v_11859 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (handleImmediateWithSignExtend v_2511 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_11860 <- eval (ror (concat (mux (eq v_11851 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_11854) v_11859);
      store v_11850 (extract v_11860 1 9) 1;
      v_11863 <- eval (extract v_11859 1 9);
      v_11864 <- eval (eq v_11863 (expression.bv_nat 8 1));
      v_11871 <- eval (eq v_11863 (expression.bv_nat 8 0));
      v_11874 <- getRegister of;
      setRegister cf (isBitSet v_11860 0);
      setRegister of (bit_or (bit_and v_11864 (notBool_ (eq (isBitSet v_11860 1) (isBitSet v_11860 2)))) (bit_and (notBool_ v_11864) (bit_or (bit_and (notBool_ v_11871) undef) (bit_and v_11871 (eq v_11874 (expression.bv_nat 1 1))))));
      pure ()
    pat_end
