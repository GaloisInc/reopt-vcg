def idivw1 : instruction :=
  definst "idivw" $ do
    pattern fun (v_2939 : reg (bv 16)) => do
      v_4944 <- getRegister rax;
      v_4946 <- getRegister rdx;
      v_4949 <- eval (concat (extract v_4946 48 64) (extract v_4944 48 64));
      v_4950 <- getRegister v_2939;
      setRegister rdx (concat (extract v_4946 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int16 v_4949 v_4950));
      setRegister rax (concat (extract v_4944 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int16 v_4949 v_4950));
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2935 : Mem) => do
      v_8393 <- getRegister rax;
      v_8395 <- getRegister rdx;
      v_8398 <- eval (concat (extract v_8395 48 64) (extract v_8393 48 64));
      v_8399 <- evaluateAddress v_2935;
      v_8400 <- load v_8399 2;
      setRegister rdx (concat (extract v_8395 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int16 v_8398 v_8400));
      setRegister rax (concat (extract v_8393 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int16 v_8398 v_8400));
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
