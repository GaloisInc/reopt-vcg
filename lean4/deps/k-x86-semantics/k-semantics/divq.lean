def divq1 : instruction :=
  definst "divq" $ do
    pattern fun (v_2742 : reg (bv 64)) => do
      v_4582 <- getRegister rdx;
      v_4583 <- getRegister rax;
      v_4584 <- eval (concat v_4582 v_4583);
      v_4585 <- getRegister v_2742;
      setRegister rdx (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int64 v_4584 v_4585);
      setRegister rax (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int64 v_4584 v_4585);
      setRegister of undef;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end;
    pattern fun (v_2739 : Mem) => do
      v_8322 <- getRegister rdx;
      v_8323 <- getRegister rax;
      v_8324 <- eval (concat v_8322 v_8323);
      v_8325 <- evaluateAddress v_2739;
      v_8326 <- load v_8325 8;
      setRegister rdx (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int64 v_8324 v_8326);
      setRegister rax (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int64 v_8324 v_8326);
      setRegister of undef;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end
