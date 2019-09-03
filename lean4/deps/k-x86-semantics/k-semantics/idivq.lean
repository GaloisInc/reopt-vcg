def idivq1 : instruction :=
  definst "idivq" $ do
    pattern fun (v_2879 : reg (bv 64)) => do
      v_5280 <- getRegister rdx;
      v_5281 <- getRegister rax;
      v_5282 <- eval (concat v_5280 v_5281);
      v_5283 <- getRegister v_2879;
      setRegister rdx (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int64 v_5282 v_5283);
      setRegister rax (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int64 v_5282 v_5283);
      setRegister of undef;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end;
    pattern fun (v_2875 : Mem) => do
      v_9232 <- getRegister rdx;
      v_9233 <- getRegister rax;
      v_9234 <- eval (concat v_9232 v_9233);
      v_9235 <- evaluateAddress v_2875;
      v_9236 <- load v_9235 8;
      setRegister rdx (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int64 v_9234 v_9236);
      setRegister rax (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int64 v_9234 v_9236);
      setRegister of undef;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end
