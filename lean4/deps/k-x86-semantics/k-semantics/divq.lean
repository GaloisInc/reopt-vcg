def divq1 : instruction :=
  definst "divq" $ do
    pattern fun (v_2833 : reg (bv 64)) => do
      v_4596 <- getRegister rdx;
      v_4597 <- getRegister rax;
      v_4598 <- eval (concat v_4596 v_4597);
      v_4599 <- getRegister v_2833;
      setRegister rax (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int64 v_4598 v_4599);
      setRegister rdx (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int64 v_4598 v_4599);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2830 : Mem) => do
      v_8110 <- getRegister rdx;
      v_8111 <- getRegister rax;
      v_8112 <- eval (concat v_8110 v_8111);
      v_8113 <- evaluateAddress v_2830;
      v_8114 <- load v_8113 8;
      setRegister rax (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int64 v_8112 v_8114);
      setRegister rdx (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int64 v_8112 v_8114);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
