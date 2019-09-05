def idivl1 : instruction :=
  definst "idivl" $ do
    pattern fun (v_2925 : reg (bv 32)) => do
      v_4908 <- getRegister rdx;
      v_4910 <- getRegister rax;
      v_4912 <- eval (concat (extract v_4908 32 64) (extract v_4910 32 64));
      v_4913 <- getRegister v_2925;
      setRegister edx (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int32 v_4912 v_4913);
      setRegister eax (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int32 v_4912 v_4913);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2921 : Mem) => do
      v_8361 <- getRegister rdx;
      v_8363 <- getRegister rax;
      v_8365 <- eval (concat (extract v_8361 32 64) (extract v_8363 32 64));
      v_8366 <- evaluateAddress v_2921;
      v_8367 <- load v_8366 4;
      setRegister edx (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int32 v_8365 v_8367);
      setRegister eax (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int32 v_8365 v_8367);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
