def imull1 : instruction :=
  definst "imull" $ do
    pattern fun (v_2904 : reg (bv 32)) => do
      v_5363 <- getRegister v_2904;
      v_5365 <- getRegister rax;
      v_5368 <- eval (mul (leanSignExtend v_5363 64) (leanSignExtend (extract v_5365 32 64) 64));
      v_5369 <- eval (extract v_5368 32 64);
      v_5373 <- eval (mux (notBool_ (eq v_5368 (leanSignExtend v_5369 64))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister edx (extract v_5368 0 32);
      setRegister eax v_5369;
      setRegister of v_5373;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_5373;
      pure ()
    pat_end;
    pattern fun (v_2917 : reg (bv 32)) (v_2918 : reg (bv 32)) => do
      v_5392 <- getRegister v_2918;
      v_5394 <- getRegister v_2917;
      v_5396 <- eval (mul (leanSignExtend v_5392 64) (leanSignExtend v_5394 64));
      v_5397 <- eval (extract v_5396 32 64);
      v_5401 <- eval (mux (notBool_ (eq v_5396 (leanSignExtend v_5397 64))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2918) v_5397;
      setRegister of v_5401;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_5401;
      pure ()
    pat_end;
    pattern fun (v_2921 : imm int) (v_2923 : reg (bv 32)) (v_2924 : reg (bv 32)) => do
      v_5409 <- getRegister v_2923;
      v_5413 <- eval (mul (leanSignExtend v_5409 64) (leanSignExtend (handleImmediateWithSignExtend v_2921 32 32) 64));
      v_5414 <- eval (extract v_5413 32 64);
      v_5418 <- eval (mux (notBool_ (eq v_5413 (leanSignExtend v_5414 64))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2924) v_5414;
      setRegister of v_5418;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_5418;
      pure ()
    pat_end;
    pattern fun (v_2900 : Mem) => do
      v_9289 <- evaluateAddress v_2900;
      v_9290 <- load v_9289 4;
      v_9292 <- getRegister rax;
      v_9295 <- eval (mul (leanSignExtend v_9290 64) (leanSignExtend (extract v_9292 32 64) 64));
      v_9296 <- eval (extract v_9295 32 64);
      v_9300 <- eval (mux (notBool_ (eq v_9295 (leanSignExtend v_9296 64))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister edx (extract v_9295 0 32);
      setRegister eax v_9296;
      setRegister of v_9300;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_9300;
      pure ()
    pat_end;
    pattern fun (v_2907 : Mem) (v_2908 : reg (bv 32)) => do
      v_9310 <- getRegister v_2908;
      v_9312 <- evaluateAddress v_2907;
      v_9313 <- load v_9312 4;
      v_9315 <- eval (mul (leanSignExtend v_9310 64) (leanSignExtend v_9313 64));
      v_9316 <- eval (extract v_9315 32 64);
      v_9320 <- eval (mux (notBool_ (eq v_9315 (leanSignExtend v_9316 64))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2908) v_9316;
      setRegister of v_9320;
      setRegister pf undef;
      setRegister af undef;
      setRegister zf undef;
      setRegister sf undef;
      setRegister cf v_9320;
      pure ()
    pat_end;
    pattern fun (v_2912 : imm int) (v_2911 : Mem) (v_2913 : reg (bv 32)) => do
      v_9328 <- evaluateAddress v_2911;
      v_9329 <- load v_9328 4;
      v_9333 <- eval (mul (leanSignExtend v_9329 64) (leanSignExtend (handleImmediateWithSignExtend v_2912 32 32) 64));
      v_9334 <- eval (extract v_9333 32 64);
      v_9338 <- eval (mux (notBool_ (eq v_9333 (leanSignExtend v_9334 64))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2913) v_9334;
      setRegister of v_9338;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_9338;
      pure ()
    pat_end
