def divb1 : instruction :=
  definst "divb" $ do
    pattern fun (v_2774 : reg (bv 8)) => do
      v_4484 <- getRegister rax;
      v_4486 <- eval (extract v_4484 48 64);
      v_4487 <- getRegister v_2774;
      setRegister rax (concat (concat (extract v_4484 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int8 v_4486 v_4487)) (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int8 v_4486 v_4487));
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2767 : Mem) => do
      v_8019 <- getRegister rax;
      v_8021 <- eval (extract v_8019 48 64);
      v_8022 <- evaluateAddress v_2767;
      v_8023 <- load v_8022 1;
      setRegister rax (concat (concat (extract v_8019 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int8 v_8021 v_8023)) (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int8 v_8021 v_8023));
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
