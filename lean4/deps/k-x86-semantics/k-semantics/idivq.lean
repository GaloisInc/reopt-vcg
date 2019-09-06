def idivq1 : instruction :=
  definst "idivq" $ do
    pattern fun (v_2958 : reg (bv 64)) => do
      v_4948 <- getRegister rdx;
      v_4949 <- getRegister rax;
      v_4950 <- eval (concat v_4948 v_4949);
      v_4951 <- getRegister v_2958;
      setRegister rax (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int64 v_4950 v_4951);
      setRegister rdx (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int64 v_4950 v_4951);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2955 : Mem) => do
      v_8388 <- getRegister rdx;
      v_8389 <- getRegister rax;
      v_8390 <- eval (concat v_8388 v_8389);
      v_8391 <- evaluateAddress v_2955;
      v_8392 <- load v_8391 8;
      setRegister rax (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int64 v_8390 v_8392);
      setRegister rdx (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int64 v_8390 v_8392);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
