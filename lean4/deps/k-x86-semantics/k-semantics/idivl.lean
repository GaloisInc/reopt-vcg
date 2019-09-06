def idivl1 : instruction :=
  definst "idivl" $ do
    pattern fun (v_2951 : reg (bv 32)) => do
      v_4929 <- getRegister rdx;
      v_4931 <- getRegister rax;
      v_4933 <- eval (concat (extract v_4929 32 64) (extract v_4931 32 64));
      v_4934 <- getRegister v_2951;
      setRegister eax (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int32 v_4933 v_4934);
      setRegister edx (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int32 v_4933 v_4934);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2948 : Mem) => do
      v_8371 <- getRegister rdx;
      v_8373 <- getRegister rax;
      v_8375 <- eval (concat (extract v_8371 32 64) (extract v_8373 32 64));
      v_8376 <- evaluateAddress v_2948;
      v_8377 <- load v_8376 4;
      setRegister eax (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int32 v_8375 v_8377);
      setRegister edx (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int32 v_8375 v_8377);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
