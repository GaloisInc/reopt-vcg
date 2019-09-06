def imull1 : instruction :=
  definst "imull" $ do
    pattern fun (v_2983 : reg (bv 32)) => do
      v_5029 <- getRegister v_2983;
      v_5031 <- getRegister rax;
      v_5034 <- eval (mul (sext v_5029 64) (sext (extract v_5031 32 64) 64));
      v_5035 <- eval (extract v_5034 32 64);
      v_5038 <- eval (notBool_ (eq v_5034 (sext v_5035 64)));
      setRegister eax v_5035;
      setRegister edx (extract v_5034 0 32);
      setRegister af undef;
      setRegister cf v_5038;
      setRegister of v_5038;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2996 : reg (bv 32)) (v_2997 : reg (bv 32)) => do
      v_5057 <- getRegister v_2997;
      v_5059 <- getRegister v_2996;
      v_5061 <- eval (mul (sext v_5057 64) (sext v_5059 64));
      v_5062 <- eval (extract v_5061 32 64);
      v_5065 <- eval (notBool_ (eq v_5061 (sext v_5062 64)));
      setRegister (lhs.of_reg v_2997) v_5062;
      setRegister af undef;
      setRegister cf v_5065;
      setRegister of v_5065;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_3001 : imm int) (v_3002 : reg (bv 32)) (v_3003 : reg (bv 32)) => do
      v_5073 <- getRegister v_3002;
      v_5077 <- eval (mul (sext v_5073 64) (sext (handleImmediateWithSignExtend v_3001 32 32) 64));
      v_5078 <- eval (extract v_5077 32 64);
      v_5081 <- eval (notBool_ (eq v_5077 (sext v_5078 64)));
      setRegister (lhs.of_reg v_3003) v_5078;
      setRegister af undef;
      setRegister cf v_5081;
      setRegister of v_5081;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2980 : Mem) => do
      v_8444 <- evaluateAddress v_2980;
      v_8445 <- load v_8444 4;
      v_8447 <- getRegister rax;
      v_8450 <- eval (mul (sext v_8445 64) (sext (extract v_8447 32 64) 64));
      v_8451 <- eval (extract v_8450 32 64);
      v_8454 <- eval (notBool_ (eq v_8450 (sext v_8451 64)));
      setRegister eax v_8451;
      setRegister edx (extract v_8450 0 32);
      setRegister af undef;
      setRegister cf v_8454;
      setRegister of v_8454;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2987 : Mem) (v_2988 : reg (bv 32)) => do
      v_8464 <- getRegister v_2988;
      v_8466 <- evaluateAddress v_2987;
      v_8467 <- load v_8466 4;
      v_8469 <- eval (mul (sext v_8464 64) (sext v_8467 64));
      v_8470 <- eval (extract v_8469 32 64);
      v_8473 <- eval (notBool_ (eq v_8469 (sext v_8470 64)));
      setRegister (lhs.of_reg v_2988) v_8470;
      setRegister af undef;
      setRegister cf v_8473;
      setRegister of v_8473;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2992 : imm int) (v_2991 : Mem) (v_2993 : reg (bv 32)) => do
      v_8481 <- evaluateAddress v_2991;
      v_8482 <- load v_8481 4;
      v_8486 <- eval (mul (sext v_8482 64) (sext (handleImmediateWithSignExtend v_2992 32 32) 64));
      v_8487 <- eval (extract v_8486 32 64);
      v_8490 <- eval (notBool_ (eq v_8486 (sext v_8487 64)));
      setRegister (lhs.of_reg v_2993) v_8487;
      setRegister af undef;
      setRegister cf v_8490;
      setRegister of v_8490;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
