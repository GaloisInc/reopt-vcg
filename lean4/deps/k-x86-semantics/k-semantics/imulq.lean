def imulq1 : instruction :=
  definst "imulq" $ do
    pattern fun (v_2931 : reg (bv 64)) => do
      v_5429 <- getRegister v_2931;
      v_5431 <- getRegister rax;
      v_5433 <- eval (mul (leanSignExtend v_5429 128) (leanSignExtend v_5431 128));
      v_5434 <- eval (extract v_5433 64 128);
      v_5438 <- eval (mux (notBool_ (eq v_5433 (leanSignExtend v_5434 128))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister rdx (extract v_5433 0 64);
      setRegister rax v_5434;
      setRegister of v_5438;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_5438;
      pure ()
    pat_end;
    pattern fun (v_2944 : reg (bv 64)) (v_2945 : reg (bv 64)) => do
      v_5457 <- getRegister v_2945;
      v_5459 <- getRegister v_2944;
      v_5461 <- eval (mul (leanSignExtend v_5457 128) (leanSignExtend v_5459 128));
      v_5462 <- eval (extract v_5461 64 128);
      v_5466 <- eval (mux (notBool_ (eq v_5461 (leanSignExtend v_5462 128))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2945) v_5462;
      setRegister of v_5466;
      setRegister pf undef;
      setRegister af undef;
      setRegister zf undef;
      setRegister sf undef;
      setRegister cf v_5466;
      pure ()
    pat_end;
    pattern fun (v_2948 : imm int) (v_2950 : reg (bv 64)) (v_2951 : reg (bv 64)) => do
      v_5474 <- getRegister v_2950;
      v_5478 <- eval (mul (leanSignExtend v_5474 128) (leanSignExtend (handleImmediateWithSignExtend v_2948 32 32) 128));
      v_5479 <- eval (extract v_5478 64 128);
      v_5483 <- eval (mux (notBool_ (eq v_5478 (leanSignExtend v_5479 128))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2951) v_5479;
      setRegister of v_5483;
      setRegister pf undef;
      setRegister af undef;
      setRegister zf undef;
      setRegister sf undef;
      setRegister cf v_5483;
      pure ()
    pat_end;
    pattern fun (v_2927 : Mem) => do
      v_9346 <- evaluateAddress v_2927;
      v_9347 <- load v_9346 8;
      v_9349 <- getRegister rax;
      v_9351 <- eval (mul (leanSignExtend v_9347 128) (leanSignExtend v_9349 128));
      v_9352 <- eval (extract v_9351 64 128);
      v_9356 <- eval (mux (notBool_ (eq v_9351 (leanSignExtend v_9352 128))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister rdx (extract v_9351 0 64);
      setRegister rax v_9352;
      setRegister of v_9356;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_9356;
      pure ()
    pat_end;
    pattern fun (v_2934 : Mem) (v_2935 : reg (bv 64)) => do
      v_9366 <- getRegister v_2935;
      v_9368 <- evaluateAddress v_2934;
      v_9369 <- load v_9368 8;
      v_9371 <- eval (mul (leanSignExtend v_9366 128) (leanSignExtend v_9369 128));
      v_9372 <- eval (extract v_9371 64 128);
      v_9376 <- eval (mux (notBool_ (eq v_9371 (leanSignExtend v_9372 128))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2935) v_9372;
      setRegister of v_9376;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_9376;
      pure ()
    pat_end;
    pattern fun (v_2939 : imm int) (v_2938 : Mem) (v_2940 : reg (bv 64)) => do
      v_9384 <- evaluateAddress v_2938;
      v_9385 <- load v_9384 8;
      v_9389 <- eval (mul (leanSignExtend v_9385 128) (leanSignExtend (handleImmediateWithSignExtend v_2939 32 32) 128));
      v_9390 <- eval (extract v_9389 64 128);
      v_9394 <- eval (mux (notBool_ (eq v_9389 (leanSignExtend v_9390 128))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2940) v_9390;
      setRegister of v_9394;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_9394;
      pure ()
    pat_end
