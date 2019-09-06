def idivw1 : instruction :=
  definst "idivw" $ do
    pattern fun (v_2965 : reg (bv 16)) => do
      v_4965 <- getRegister rdx;
      v_4968 <- getRegister rax;
      v_4970 <- eval (concat (extract v_4965 48 64) (extract v_4968 48 64));
      v_4971 <- getRegister v_2965;
      setRegister rax (concat (extract v_4968 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int16 v_4970 v_4971));
      setRegister rdx (concat (extract v_4965 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int16 v_4970 v_4971));
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2962 : Mem) => do
      v_8403 <- getRegister rdx;
      v_8406 <- getRegister rax;
      v_8408 <- eval (concat (extract v_8403 48 64) (extract v_8406 48 64));
      v_8409 <- evaluateAddress v_2962;
      v_8410 <- load v_8409 2;
      setRegister rax (concat (extract v_8406 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int16 v_8408 v_8410));
      setRegister rdx (concat (extract v_8403 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int16 v_8408 v_8410));
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
