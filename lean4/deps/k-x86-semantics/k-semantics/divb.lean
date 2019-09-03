def divb1 : instruction :=
  definst "divb" $ do
    pattern fun (v_2706 : reg (bv 8)) => do
      v_4476 <- getRegister rax;
      v_4478 <- eval (extract v_4476 48 64);
      v_4479 <- getRegister v_2706;
      setRegister rax (concat (concat (extract v_4476 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int8 v_4478 v_4479)) (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int8 v_4478 v_4479));
      setRegister of undef;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end;
    pattern fun (v_2703 : Mem) => do
      v_8241 <- getRegister rax;
      v_8243 <- eval (extract v_8241 48 64);
      v_8244 <- evaluateAddress v_2703;
      v_8245 <- load v_8244 1;
      setRegister rax (concat (concat (extract v_8241 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int8 v_8243 v_8245)) (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int8 v_8243 v_8245));
      setRegister of undef;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end
