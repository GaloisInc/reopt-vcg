def andq1 : instruction :=
  definst "andq" $ do
    pattern fun (v_2844 : imm int) (v_2846 : reg (bv 64)) => do
      v_5471 <- getRegister v_2846;
      v_5472 <- eval (handleImmediateWithSignExtend v_2844 32 32);
      v_5475 <- eval (bv_and v_5471 (mi 64 (svalueMInt v_5472)));
      setRegister (lhs.of_reg v_2846) v_5475;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_5471 63 64) (extract v_5472 31 32)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_5471 62 63) (extract v_5472 30 31)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5471 61 62) (extract v_5472 29 30)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5471 60 61) (extract v_5472 28 29)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5471 59 60) (extract v_5472 27 28)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5471 58 59) (extract v_5472 26 27)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5471 57 58) (extract v_5472 25 26)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5471 56 57) (extract v_5472 24 25)) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_5475);
      setRegister af undef;
      setRegister sf (extract v_5475 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2854 : reg (bv 64)) (v_2855 : reg (bv 64)) => do
      v_5535 <- getRegister v_2855;
      v_5536 <- getRegister v_2854;
      v_5537 <- eval (bv_and v_5535 v_5536);
      setRegister (lhs.of_reg v_2855) v_5537;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_5537 56 64));
      setRegister zf (zeroFlag v_5537);
      setRegister af undef;
      setRegister sf (extract v_5537 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2849 : Mem) (v_2850 : reg (bv 64)) => do
      v_9409 <- getRegister v_2850;
      v_9410 <- evaluateAddress v_2849;
      v_9411 <- load v_9410 8;
      v_9412 <- eval (bv_and v_9409 v_9411);
      setRegister (lhs.of_reg v_2850) v_9412;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9412 56 64));
      setRegister zf (zeroFlag v_9412);
      setRegister af undef;
      setRegister sf (extract v_9412 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2837 : imm int) (v_2836 : Mem) => do
      v_10944 <- evaluateAddress v_2836;
      v_10945 <- load v_10944 8;
      v_10946 <- eval (handleImmediateWithSignExtend v_2837 32 32);
      v_10949 <- eval (bv_and v_10945 (mi 64 (svalueMInt v_10946)));
      store v_10944 v_10949 8;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_10945 63 64) (extract v_10946 31 32)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_10945 62 63) (extract v_10946 30 31)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_10945 61 62) (extract v_10946 29 30)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_10945 60 61) (extract v_10946 28 29)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_10945 59 60) (extract v_10946 27 28)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_10945 58 59) (extract v_10946 26 27)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_10945 57 58) (extract v_10946 25 26)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_10945 56 57) (extract v_10946 24 25)) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (zeroFlag v_10949);
      setRegister sf (extract v_10949 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2841 : reg (bv 64)) (v_2840 : Mem) => do
      v_11005 <- evaluateAddress v_2840;
      v_11006 <- load v_11005 8;
      v_11007 <- getRegister v_2841;
      v_11008 <- eval (bv_and v_11006 v_11007);
      store v_11005 v_11008 8;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_11008 56 64));
      setRegister af undef;
      setRegister zf (zeroFlag v_11008);
      setRegister sf (extract v_11008 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
