def idivl1 : instruction :=
  definst "idivl" $ do
    pattern fun (v_2860 : reg (bv 32)) => do
      v_4931 <- getRegister rdx;
      v_4933 <- getRegister rax;
      v_4935 <- eval (concat (extract v_4931 32 64) (extract v_4933 32 64));
      v_4936 <- getRegister v_2860;
      setRegister edx (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int32 v_4935 v_4936);
      setRegister eax (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int32 v_4935 v_4936);
      setRegister of undef;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end;
    pattern fun (v_2857 : Mem) => do
      v_8595 <- getRegister rdx;
      v_8597 <- getRegister rax;
      v_8599 <- eval (concat (extract v_8595 32 64) (extract v_8597 32 64));
      v_8600 <- evaluateAddress v_2857;
      v_8601 <- load v_8600 4;
      setRegister edx (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int32 v_8599 v_8601);
      setRegister eax (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int32 v_8599 v_8601);
      setRegister of undef;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end
