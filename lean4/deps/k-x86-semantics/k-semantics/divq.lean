def divq1 : instruction :=
  definst "divq" $ do
    pattern fun (v_2754 : reg (bv 64)) => do
      v_4674 <- getRegister rdx;
      v_4675 <- getRegister rax;
      v_4676 <- eval (concat v_4674 v_4675);
      v_4677 <- getRegister v_2754;
      setRegister rdx (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int64 v_4676 v_4677);
      setRegister rax (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int64 v_4676 v_4677);
      setRegister of undef;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end;
    pattern fun (v_2750 : Mem) => do
      v_8702 <- getRegister rdx;
      v_8703 <- getRegister rax;
      v_8704 <- eval (concat v_8702 v_8703);
      v_8705 <- evaluateAddress v_2750;
      v_8706 <- load v_8705 8;
      setRegister rdx (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int64 v_8704 v_8706);
      setRegister rax (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int64 v_8704 v_8706);
      setRegister of undef;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end
