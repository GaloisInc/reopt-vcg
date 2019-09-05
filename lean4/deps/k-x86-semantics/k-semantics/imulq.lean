def imulq1 : instruction :=
  definst "imulq" $ do
    pattern fun (v_2983 : reg (bv 64)) => do
      v_5071 <- getRegister v_2983;
      v_5073 <- getRegister rax;
      v_5075 <- eval (mul (sext v_5071 128) (sext v_5073 128));
      v_5076 <- eval (extract v_5075 64 128);
      v_5079 <- eval (notBool_ (eq v_5075 (sext v_5076 128)));
      setRegister rdx (extract v_5075 0 64);
      setRegister rax v_5076;
      setRegister af undef;
      setRegister cf v_5079;
      setRegister of v_5079;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2996 : reg (bv 64)) (v_2997 : reg (bv 64)) => do
      v_5098 <- getRegister v_2997;
      v_5100 <- getRegister v_2996;
      v_5102 <- eval (mul (sext v_5098 128) (sext v_5100 128));
      v_5103 <- eval (extract v_5102 64 128);
      v_5106 <- eval (notBool_ (eq v_5102 (sext v_5103 128)));
      setRegister (lhs.of_reg v_2997) v_5103;
      setRegister af undef;
      setRegister cf v_5106;
      setRegister of v_5106;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_3004 : imm int) (v_3001 : reg (bv 64)) (v_3002 : reg (bv 64)) => do
      v_5114 <- getRegister v_3001;
      v_5118 <- eval (mul (sext v_5114 128) (sext (handleImmediateWithSignExtend v_3004 32 32) 128));
      v_5119 <- eval (extract v_5118 64 128);
      v_5122 <- eval (notBool_ (eq v_5118 (sext v_5119 128)));
      setRegister (lhs.of_reg v_3002) v_5119;
      setRegister af undef;
      setRegister cf v_5122;
      setRegister of v_5122;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2980 : Mem) => do
      v_8488 <- evaluateAddress v_2980;
      v_8489 <- load v_8488 8;
      v_8491 <- getRegister rax;
      v_8493 <- eval (mul (sext v_8489 128) (sext v_8491 128));
      v_8494 <- eval (extract v_8493 64 128);
      v_8497 <- eval (notBool_ (eq v_8493 (sext v_8494 128)));
      setRegister rdx (extract v_8493 0 64);
      setRegister rax v_8494;
      setRegister af undef;
      setRegister cf v_8497;
      setRegister of v_8497;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2987 : Mem) (v_2988 : reg (bv 64)) => do
      v_8507 <- getRegister v_2988;
      v_8509 <- evaluateAddress v_2987;
      v_8510 <- load v_8509 8;
      v_8512 <- eval (mul (sext v_8507 128) (sext v_8510 128));
      v_8513 <- eval (extract v_8512 64 128);
      v_8516 <- eval (notBool_ (eq v_8512 (sext v_8513 128)));
      setRegister (lhs.of_reg v_2988) v_8513;
      setRegister af undef;
      setRegister cf v_8516;
      setRegister of v_8516;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2993 : imm int) (v_2991 : Mem) (v_2992 : reg (bv 64)) => do
      v_8524 <- evaluateAddress v_2991;
      v_8525 <- load v_8524 8;
      v_8529 <- eval (mul (sext v_8525 128) (sext (handleImmediateWithSignExtend v_2993 32 32) 128));
      v_8530 <- eval (extract v_8529 64 128);
      v_8533 <- eval (notBool_ (eq v_8529 (sext v_8530 128)));
      setRegister (lhs.of_reg v_2992) v_8530;
      setRegister af undef;
      setRegister cf v_8533;
      setRegister of v_8533;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
