def idivb1 : instruction :=
  definst "idivb" $ do
    pattern fun (v_2945 : reg (bv 8)) => do
      v_4911 <- getRegister rax;
      v_4913 <- eval (extract v_4911 48 64);
      v_4914 <- getRegister v_2945;
      setRegister rax (concat (concat (extract v_4911 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int8 v_4913 v_4914)) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int8 v_4913 v_4914));
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2937 : Mem) => do
      v_8355 <- getRegister rax;
      v_8357 <- eval (extract v_8355 48 64);
      v_8358 <- evaluateAddress v_2937;
      v_8359 <- load v_8358 1;
      setRegister rax (concat (concat (extract v_8355 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int8 v_8357 v_8359)) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int8 v_8357 v_8359));
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
