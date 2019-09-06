def imulb1 : instruction :=
  definst "imulb" $ do
    pattern fun (v_2977 : reg (bv 8)) => do
      v_5007 <- getRegister v_2977;
      v_5009 <- getRegister rax;
      v_5012 <- eval (mul (sext v_5007 16) (sext (extract v_5009 56 64) 16));
      v_5016 <- eval (notBool_ (eq v_5012 (sext (extract v_5012 8 16) 16)));
      setRegister rax (concat (extract v_5009 0 48) v_5012);
      setRegister af undef;
      setRegister cf v_5016;
      setRegister of v_5016;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2969 : Mem) => do
      v_8424 <- evaluateAddress v_2969;
      v_8425 <- load v_8424 1;
      v_8427 <- getRegister rax;
      v_8430 <- eval (mul (sext v_8425 16) (sext (extract v_8427 56 64) 16));
      v_8434 <- eval (notBool_ (eq v_8430 (sext (extract v_8430 8 16) 16)));
      setRegister rax (concat (extract v_8427 0 48) v_8430);
      setRegister af undef;
      setRegister cf v_8434;
      setRegister of v_8434;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
