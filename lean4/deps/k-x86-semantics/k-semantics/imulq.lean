def imulq1 : instruction :=
  definst "imulq" $ do
    pattern fun (v_3010 : reg (bv 64)) => do
      v_5092 <- getRegister v_3010;
      v_5094 <- getRegister rax;
      v_5096 <- eval (mul (sext v_5092 128) (sext v_5094 128));
      v_5097 <- eval (extract v_5096 64 128);
      v_5100 <- eval (notBool_ (eq v_5096 (sext v_5097 128)));
      setRegister rax v_5097;
      setRegister rdx (extract v_5096 0 64);
      setRegister af undef;
      setRegister cf v_5100;
      setRegister of v_5100;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_3023 : reg (bv 64)) (v_3024 : reg (bv 64)) => do
      v_5119 <- getRegister v_3024;
      v_5121 <- getRegister v_3023;
      v_5123 <- eval (mul (sext v_5119 128) (sext v_5121 128));
      v_5124 <- eval (extract v_5123 64 128);
      v_5127 <- eval (notBool_ (eq v_5123 (sext v_5124 128)));
      setRegister (lhs.of_reg v_3024) v_5124;
      setRegister af undef;
      setRegister cf v_5127;
      setRegister of v_5127;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_3028 : imm int) (v_3029 : reg (bv 64)) (v_3030 : reg (bv 64)) => do
      v_5135 <- getRegister v_3029;
      v_5139 <- eval (mul (sext v_5135 128) (sext (handleImmediateWithSignExtend v_3028 32 32) 128));
      v_5140 <- eval (extract v_5139 64 128);
      v_5143 <- eval (notBool_ (eq v_5139 (sext v_5140 128)));
      setRegister (lhs.of_reg v_3030) v_5140;
      setRegister af undef;
      setRegister cf v_5143;
      setRegister of v_5143;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_3007 : Mem) => do
      v_8498 <- evaluateAddress v_3007;
      v_8499 <- load v_8498 8;
      v_8501 <- getRegister rax;
      v_8503 <- eval (mul (sext v_8499 128) (sext v_8501 128));
      v_8504 <- eval (extract v_8503 64 128);
      v_8507 <- eval (notBool_ (eq v_8503 (sext v_8504 128)));
      setRegister rax v_8504;
      setRegister rdx (extract v_8503 0 64);
      setRegister af undef;
      setRegister cf v_8507;
      setRegister of v_8507;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_3014 : Mem) (v_3015 : reg (bv 64)) => do
      v_8517 <- getRegister v_3015;
      v_8519 <- evaluateAddress v_3014;
      v_8520 <- load v_8519 8;
      v_8522 <- eval (mul (sext v_8517 128) (sext v_8520 128));
      v_8523 <- eval (extract v_8522 64 128);
      v_8526 <- eval (notBool_ (eq v_8522 (sext v_8523 128)));
      setRegister (lhs.of_reg v_3015) v_8523;
      setRegister af undef;
      setRegister cf v_8526;
      setRegister of v_8526;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_3019 : imm int) (v_3018 : Mem) (v_3020 : reg (bv 64)) => do
      v_8534 <- evaluateAddress v_3018;
      v_8535 <- load v_8534 8;
      v_8539 <- eval (mul (sext v_8535 128) (sext (handleImmediateWithSignExtend v_3019 32 32) 128));
      v_8540 <- eval (extract v_8539 64 128);
      v_8543 <- eval (notBool_ (eq v_8539 (sext v_8540 128)));
      setRegister (lhs.of_reg v_3020) v_8540;
      setRegister af undef;
      setRegister cf v_8543;
      setRegister of v_8543;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
