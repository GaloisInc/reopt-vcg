def imulw1 : instruction :=
  definst "imulw" $ do
    pattern fun (v_2959 : reg (bv 16)) => do
      v_5494 <- getRegister v_2959;
      v_5496 <- getRegister rax;
      v_5499 <- eval (mul (leanSignExtend v_5494 32) (leanSignExtend (extract v_5496 48 64) 32));
      v_5500 <- eval (extract v_5499 16 32);
      v_5504 <- eval (mux (notBool_ (eq v_5499 (leanSignExtend v_5500 32))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      v_5507 <- getRegister rdx;
      setRegister rdx (concat (extract v_5507 0 48) (extract v_5499 0 16));
      setRegister rax (concat (extract v_5496 0 48) v_5500);
      setRegister of v_5504;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_5504;
      pure ()
    pat_end;
    pattern fun (v_2972 : reg (bv 16)) (v_2973 : reg (bv 16)) => do
      v_5528 <- getRegister v_2973;
      v_5530 <- getRegister v_2972;
      v_5532 <- eval (mul (leanSignExtend v_5528 32) (leanSignExtend v_5530 32));
      v_5533 <- eval (extract v_5532 16 32);
      v_5537 <- eval (mux (notBool_ (eq v_5532 (leanSignExtend v_5533 32))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2973) v_5533;
      setRegister of v_5537;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_5537;
      pure ()
    pat_end;
    pattern fun (v_2975 : imm int) (v_2978 : reg (bv 16)) (v_2979 : reg (bv 16)) => do
      v_5545 <- getRegister v_2978;
      v_5549 <- eval (mul (leanSignExtend v_5545 32) (leanSignExtend (handleImmediateWithSignExtend v_2975 16 16) 32));
      v_5550 <- eval (extract v_5549 16 32);
      v_5554 <- eval (mux (notBool_ (eq v_5549 (leanSignExtend v_5550 32))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2979) v_5550;
      setRegister of v_5554;
      setRegister pf undef;
      setRegister af undef;
      setRegister zf undef;
      setRegister sf undef;
      setRegister cf v_5554;
      pure ()
    pat_end;
    pattern fun (v_2954 : Mem) => do
      v_9402 <- evaluateAddress v_2954;
      v_9403 <- load v_9402 2;
      v_9405 <- getRegister rax;
      v_9408 <- eval (mul (leanSignExtend v_9403 32) (leanSignExtend (extract v_9405 48 64) 32));
      v_9409 <- eval (extract v_9408 16 32);
      v_9413 <- eval (mux (notBool_ (eq v_9408 (leanSignExtend v_9409 32))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      v_9416 <- getRegister rdx;
      setRegister rdx (concat (extract v_9416 0 48) (extract v_9408 0 16));
      setRegister rax (concat (extract v_9405 0 48) v_9409);
      setRegister of v_9413;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_9413;
      pure ()
    pat_end;
    pattern fun (v_2961 : Mem) (v_2963 : reg (bv 16)) => do
      v_9428 <- getRegister v_2963;
      v_9430 <- evaluateAddress v_2961;
      v_9431 <- load v_9430 2;
      v_9433 <- eval (mul (leanSignExtend v_9428 32) (leanSignExtend v_9431 32));
      v_9434 <- eval (extract v_9433 16 32);
      v_9438 <- eval (mux (notBool_ (eq v_9433 (leanSignExtend v_9434 32))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2963) v_9434;
      setRegister of v_9438;
      setRegister pf undef;
      setRegister af undef;
      setRegister zf undef;
      setRegister sf undef;
      setRegister cf v_9438;
      pure ()
    pat_end;
    pattern fun (v_2966 : imm int) (v_2965 : Mem) (v_2968 : reg (bv 16)) => do
      v_9446 <- evaluateAddress v_2965;
      v_9447 <- load v_9446 2;
      v_9451 <- eval (mul (leanSignExtend v_9447 32) (leanSignExtend (handleImmediateWithSignExtend v_2966 16 16) 32));
      v_9452 <- eval (extract v_9451 16 32);
      v_9456 <- eval (mux (notBool_ (eq v_9451 (leanSignExtend v_9452 32))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2968) v_9452;
      setRegister of v_9456;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_9456;
      pure ()
    pat_end
