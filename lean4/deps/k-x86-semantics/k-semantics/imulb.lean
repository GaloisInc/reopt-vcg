def imulb1 : instruction :=
  definst "imulb" $ do
    pattern fun (v_2949 : reg (bv 8)) => do
      v_4986 <- getRegister v_2949;
      v_4988 <- getRegister rax;
      v_4991 <- eval (mul (sext v_4986 16) (sext (extract v_4988 56 64) 16));
      v_4995 <- eval (notBool_ (eq v_4991 (sext (extract v_4991 8 16) 16)));
      setRegister rax (concat (extract v_4988 0 48) v_4991);
      setRegister af undef;
      setRegister cf v_4995;
      setRegister of v_4995;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2942 : Mem) => do
      v_8414 <- evaluateAddress v_2942;
      v_8415 <- load v_8414 1;
      v_8417 <- getRegister rax;
      v_8420 <- eval (mul (sext v_8415 16) (sext (extract v_8417 56 64) 16));
      v_8424 <- eval (notBool_ (eq v_8420 (sext (extract v_8420 8 16) 16)));
      setRegister rax (concat (extract v_8417 0 48) v_8420);
      setRegister af undef;
      setRegister cf v_8424;
      setRegister of v_8424;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
