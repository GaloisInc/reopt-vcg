def testb1 : instruction :=
  definst "testb" $ do
    pattern fun (v_2391 : imm int) al => do
      v_3983 <- getRegister rax;
      v_3985 <- eval (handleImmediateWithSignExtend v_2391 8 8);
      v_3987 <- eval (bv_and (extract v_3983 56 57) (extract v_3985 0 1));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_3983 63 64) (extract v_3985 7 8)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_3983 62 63) (extract v_3985 6 7)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_3983 61 62) (extract v_3985 5 6)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_3983 60 61) (extract v_3985 4 5)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_3983 59 60) (extract v_3985 3 4)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_3983 58 59) (extract v_3985 2 3)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_3983 57 58) (extract v_3985 1 2)) (expression.bv_nat 1 1)))) (eq v_3987 (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (zeroFlag (bv_and (extract v_3983 56 64) v_3985));
      setRegister sf v_3987;
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2407 : imm int) (v_2409 : reg (bv 8)) => do
      v_4052 <- getRegister v_2409;
      v_4054 <- eval (bv_and v_4052 (handleImmediateWithSignExtend v_2407 8 8));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4054 0 8));
      setRegister af undef;
      setRegister zf (zeroFlag v_4054);
      setRegister sf (extract v_4054 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2413 : reg (bv 8)) (v_2414 : reg (bv 8)) => do
      v_4065 <- getRegister v_2414;
      v_4066 <- getRegister v_2413;
      v_4067 <- eval (bv_and v_4065 v_4066);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4067 0 8));
      setRegister af undef;
      setRegister zf (zeroFlag v_4067);
      setRegister sf (extract v_4067 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2396 : imm int) (v_2395 : Mem) => do
      v_9867 <- evaluateAddress v_2395;
      v_9868 <- load v_9867 1;
      v_9870 <- eval (bv_and v_9868 (handleImmediateWithSignExtend v_2396 8 8));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9870 0 8));
      setRegister af undef;
      setRegister zf (zeroFlag v_9870);
      setRegister sf (extract v_9870 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2400 : reg (bv 8)) (v_2399 : Mem) => do
      v_9881 <- evaluateAddress v_2399;
      v_9882 <- load v_9881 1;
      v_9883 <- getRegister v_2400;
      v_9884 <- eval (bv_and v_9882 v_9883);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9884 0 8));
      setRegister af undef;
      setRegister zf (zeroFlag v_9884);
      setRegister sf (extract v_9884 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
