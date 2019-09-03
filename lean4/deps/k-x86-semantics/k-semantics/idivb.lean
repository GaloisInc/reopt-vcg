def idivb1 : instruction :=
  definst "idivb" $ do
    pattern fun (v_2860 : reg (bv 8)) => do
      v_5228 <- getRegister rax;
      v_5230 <- eval (extract v_5228 48 64);
      v_5231 <- getRegister v_2860;
      setRegister rax (concat (concat (extract v_5228 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int8 v_5230 v_5231)) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int8 v_5230 v_5231));
      setRegister of undef;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end;
    pattern fun (v_2857 : Mem) => do
      v_9199 <- getRegister rax;
      v_9201 <- eval (extract v_9199 48 64);
      v_9202 <- evaluateAddress v_2857;
      v_9203 <- load v_9202 1;
      setRegister rax (concat (concat (extract v_9199 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int8 v_9201 v_9203)) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int8 v_9201 v_9203));
      setRegister of undef;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end
