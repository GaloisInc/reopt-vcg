def idivq1 : instruction :=
  definst "idivq" $ do
    pattern fun (v_2931 : reg (bv 64)) => do
      v_4927 <- getRegister rdx;
      v_4928 <- getRegister rax;
      v_4929 <- eval (concat v_4927 v_4928);
      v_4930 <- getRegister v_2931;
      setRegister rdx (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int64 v_4929 v_4930);
      setRegister rax (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int64 v_4929 v_4930);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2928 : Mem) => do
      v_8378 <- getRegister rdx;
      v_8379 <- getRegister rax;
      v_8380 <- eval (concat v_8378 v_8379);
      v_8381 <- evaluateAddress v_2928;
      v_8382 <- load v_8381 8;
      setRegister rdx (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int64 v_8380 v_8382);
      setRegister rax (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int64 v_8380 v_8382);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
