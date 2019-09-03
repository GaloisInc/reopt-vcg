def idivb1 : instruction :=
  definst "idivb" $ do
    pattern fun (v_2849 : reg (bv 8)) => do
      v_4898 <- getRegister rax;
      v_4900 <- eval (extract v_4898 48 64);
      v_4901 <- getRegister v_2849;
      setRegister rax (concat (concat (extract v_4898 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int8 v_4900 v_4901)) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int8 v_4900 v_4901));
      setRegister of undef;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end;
    pattern fun (v_2846 : Mem) => do
      v_8579 <- getRegister rax;
      v_8581 <- eval (extract v_8579 48 64);
      v_8582 <- evaluateAddress v_2846;
      v_8583 <- load v_8582 1;
      setRegister rax (concat (concat (extract v_8579 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int8 v_8581 v_8583)) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int8 v_8581 v_8583));
      setRegister of undef;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end
