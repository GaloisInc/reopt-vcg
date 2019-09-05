def divq1 : instruction :=
  definst "divq" $ do
    pattern fun (v_2806 : reg (bv 64)) => do
      v_4575 <- getRegister rdx;
      v_4576 <- getRegister rax;
      v_4577 <- eval (concat v_4575 v_4576);
      v_4578 <- getRegister v_2806;
      setRegister rdx (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int64 v_4577 v_4578);
      setRegister rax (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int64 v_4577 v_4578);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2803 : Mem) => do
      v_8100 <- getRegister rdx;
      v_8101 <- getRegister rax;
      v_8102 <- eval (concat v_8100 v_8101);
      v_8103 <- evaluateAddress v_2803;
      v_8104 <- load v_8103 8;
      setRegister rdx (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int64 v_8102 v_8104);
      setRegister rax (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int64 v_8102 v_8104);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
