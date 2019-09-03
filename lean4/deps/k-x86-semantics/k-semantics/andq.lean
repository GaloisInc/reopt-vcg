def andq1 : instruction :=
  definst "andq" $ do
    pattern fun (v_2859 : imm int) (v_2858 : reg (bv 64)) => do
      v_5636 <- getRegister v_2858;
      v_5637 <- eval (handleImmediateWithSignExtend v_2859 32 32);
      v_5639 <- eval (bv_and v_5636 (leanSignExtend v_5637 64));
      setRegister (lhs.of_reg v_2858) v_5639;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_5636 63 64) (extract v_5637 31 32)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_5636 62 63) (extract v_5637 30 31)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5636 61 62) (extract v_5637 29 30)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5636 60 61) (extract v_5637 28 29)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5636 59 60) (extract v_5637 27 28)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5636 58 59) (extract v_5637 26 27)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5636 57 58) (extract v_5637 25 26)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5636 56 57) (extract v_5637 24 25)) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_5639);
      setRegister af undef;
      setRegister sf (extract v_5639 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2867 : reg (bv 64)) (v_2868 : reg (bv 64)) => do
      v_5699 <- getRegister v_2868;
      v_5700 <- getRegister v_2867;
      v_5701 <- eval (bv_and v_5699 v_5700);
      setRegister (lhs.of_reg v_2868) v_5701;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_5701 56 64));
      setRegister zf (zeroFlag v_5701);
      setRegister af undef;
      setRegister sf (extract v_5701 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2862 : Mem) (v_2863 : reg (bv 64)) => do
      v_9705 <- getRegister v_2863;
      v_9706 <- evaluateAddress v_2862;
      v_9707 <- load v_9706 8;
      v_9708 <- eval (bv_and v_9705 v_9707);
      setRegister (lhs.of_reg v_2863) v_9708;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9708 56 64));
      setRegister zf (zeroFlag v_9708);
      setRegister af undef;
      setRegister sf (extract v_9708 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2850 : imm int) (v_2849 : Mem) => do
      v_11228 <- evaluateAddress v_2849;
      v_11229 <- load v_11228 8;
      v_11230 <- eval (handleImmediateWithSignExtend v_2850 32 32);
      v_11232 <- eval (bv_and v_11229 (leanSignExtend v_11230 64));
      store v_11228 v_11232 8;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_11229 63 64) (extract v_11230 31 32)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_11229 62 63) (extract v_11230 30 31)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_11229 61 62) (extract v_11230 29 30)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_11229 60 61) (extract v_11230 28 29)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_11229 59 60) (extract v_11230 27 28)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_11229 58 59) (extract v_11230 26 27)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_11229 57 58) (extract v_11230 25 26)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_11229 56 57) (extract v_11230 24 25)) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (zeroFlag v_11232);
      setRegister sf (extract v_11232 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2854 : reg (bv 64)) (v_2853 : Mem) => do
      v_11288 <- evaluateAddress v_2853;
      v_11289 <- load v_11288 8;
      v_11290 <- getRegister v_2854;
      v_11291 <- eval (bv_and v_11289 v_11290);
      store v_11288 v_11291 8;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_11291 56 64));
      setRegister af undef;
      setRegister zf (zeroFlag v_11291);
      setRegister sf (extract v_11291 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
