def divb1 : instruction :=
  definst "divb" $ do
    pattern fun (v_2717 : reg (bv 8)) => do
      v_4496 <- getRegister rax;
      v_4498 <- eval (extract v_4496 48 64);
      v_4499 <- getRegister v_2717;
      setRegister rax (concat (concat (extract v_4496 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int8 v_4498 v_4499)) (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int8 v_4498 v_4499));
      setRegister of undef;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end;
    pattern fun (v_2714 : Mem) => do
      v_8549 <- getRegister rax;
      v_8551 <- eval (extract v_8549 48 64);
      v_8552 <- evaluateAddress v_2714;
      v_8553 <- load v_8552 1;
      setRegister rax (concat (concat (extract v_8549 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int8 v_8551 v_8553)) (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int8 v_8551 v_8553));
      setRegister of undef;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end
