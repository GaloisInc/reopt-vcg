def testl1 : instruction :=
  definst "testl" $ do
    pattern fun (v_2424 : imm int) eax => do
      v_4117 <- getRegister rax;
      v_4119 <- eval (handleImmediateWithSignExtend v_2424 32 32);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_4117 63 64) (extract v_4119 31 32)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_4117 62 63) (extract v_4119 30 31)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4117 61 62) (extract v_4119 29 30)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4117 60 61) (extract v_4119 28 29)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4117 59 60) (extract v_4119 27 28)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4117 58 59) (extract v_4119 26 27)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4117 57 58) (extract v_4119 25 26)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4117 56 57) (extract v_4119 24 25)) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (zeroFlag (bv_and (extract v_4117 32 64) v_4119));
      setRegister sf (bv_and (extract v_4117 32 33) (extract v_4119 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2436 : imm int) (v_2438 : reg (bv 32)) => do
      v_4185 <- getRegister v_2438;
      v_4187 <- eval (bv_and v_4185 (handleImmediateWithSignExtend v_2436 32 32));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4187 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_4187);
      setRegister sf (extract v_4187 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2442 : reg (bv 32)) (v_2443 : reg (bv 32)) => do
      v_4198 <- getRegister v_2443;
      v_4199 <- getRegister v_2442;
      v_4200 <- eval (bv_and v_4198 v_4199);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4200 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_4200);
      setRegister sf (extract v_4200 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2429 : imm int) (v_2428 : Mem) => do
      v_8814 <- evaluateAddress v_2428;
      v_8815 <- load v_8814 4;
      v_8817 <- eval (bv_and v_8815 (handleImmediateWithSignExtend v_2429 32 32));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_8817 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_8817);
      setRegister sf (extract v_8817 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2433 : reg (bv 32)) (v_2432 : Mem) => do
      v_8828 <- evaluateAddress v_2432;
      v_8829 <- load v_8828 4;
      v_8830 <- getRegister v_2433;
      v_8831 <- eval (bv_and v_8829 v_8830);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_8831 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_8831);
      setRegister sf (extract v_8831 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
