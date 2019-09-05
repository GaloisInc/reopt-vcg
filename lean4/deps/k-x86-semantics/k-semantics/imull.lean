def imull1 : instruction :=
  definst "imull" $ do
    pattern fun (v_2957 : reg (bv 32)) => do
      v_5008 <- getRegister v_2957;
      v_5010 <- getRegister rax;
      v_5013 <- eval (mul (sext v_5008 64) (sext (extract v_5010 32 64) 64));
      v_5014 <- eval (extract v_5013 32 64);
      v_5017 <- eval (notBool_ (eq v_5013 (sext v_5014 64)));
      setRegister edx (extract v_5013 0 32);
      setRegister eax v_5014;
      setRegister af undef;
      setRegister cf v_5017;
      setRegister of v_5017;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2970 : reg (bv 32)) (v_2971 : reg (bv 32)) => do
      v_5036 <- getRegister v_2971;
      v_5038 <- getRegister v_2970;
      v_5040 <- eval (mul (sext v_5036 64) (sext v_5038 64));
      v_5041 <- eval (extract v_5040 32 64);
      v_5044 <- eval (notBool_ (eq v_5040 (sext v_5041 64)));
      setRegister (lhs.of_reg v_2971) v_5041;
      setRegister af undef;
      setRegister cf v_5044;
      setRegister of v_5044;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2977 : imm int) (v_2975 : reg (bv 32)) (v_2976 : reg (bv 32)) => do
      v_5052 <- getRegister v_2975;
      v_5056 <- eval (mul (sext v_5052 64) (sext (handleImmediateWithSignExtend v_2977 32 32) 64));
      v_5057 <- eval (extract v_5056 32 64);
      v_5060 <- eval (notBool_ (eq v_5056 (sext v_5057 64)));
      setRegister (lhs.of_reg v_2976) v_5057;
      setRegister af undef;
      setRegister cf v_5060;
      setRegister of v_5060;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2953 : Mem) => do
      v_8434 <- evaluateAddress v_2953;
      v_8435 <- load v_8434 4;
      v_8437 <- getRegister rax;
      v_8440 <- eval (mul (sext v_8435 64) (sext (extract v_8437 32 64) 64));
      v_8441 <- eval (extract v_8440 32 64);
      v_8444 <- eval (notBool_ (eq v_8440 (sext v_8441 64)));
      setRegister edx (extract v_8440 0 32);
      setRegister eax v_8441;
      setRegister af undef;
      setRegister cf v_8444;
      setRegister of v_8444;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2960 : Mem) (v_2961 : reg (bv 32)) => do
      v_8454 <- getRegister v_2961;
      v_8456 <- evaluateAddress v_2960;
      v_8457 <- load v_8456 4;
      v_8459 <- eval (mul (sext v_8454 64) (sext v_8457 64));
      v_8460 <- eval (extract v_8459 32 64);
      v_8463 <- eval (notBool_ (eq v_8459 (sext v_8460 64)));
      setRegister (lhs.of_reg v_2961) v_8460;
      setRegister af undef;
      setRegister cf v_8463;
      setRegister of v_8463;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2966 : imm int) (v_2964 : Mem) (v_2965 : reg (bv 32)) => do
      v_8471 <- evaluateAddress v_2964;
      v_8472 <- load v_8471 4;
      v_8476 <- eval (mul (sext v_8472 64) (sext (handleImmediateWithSignExtend v_2966 32 32) 64));
      v_8477 <- eval (extract v_8476 32 64);
      v_8480 <- eval (notBool_ (eq v_8476 (sext v_8477 64)));
      setRegister (lhs.of_reg v_2965) v_8477;
      setRegister af undef;
      setRegister cf v_8480;
      setRegister of v_8480;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
