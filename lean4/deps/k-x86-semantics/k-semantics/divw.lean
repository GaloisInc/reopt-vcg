def divw1 : instruction :=
  definst "divw" $ do
    pattern fun (v_2767 : reg (bv 16)) => do
      v_4629 <- getRegister rax;
      v_4631 <- getRegister rdx;
      v_4634 <- eval (concat (extract v_4631 48 64) (extract v_4629 48 64));
      v_4635 <- getRegister v_2767;
      setRegister rdx (concat (extract v_4631 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int16 v_4634 v_4635));
      setRegister rax (concat (extract v_4629 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int16 v_4634 v_4635));
      setRegister of undef;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end;
    pattern fun (v_2764 : Mem) => do
      v_8359 <- getRegister rax;
      v_8361 <- getRegister rdx;
      v_8364 <- eval (concat (extract v_8361 48 64) (extract v_8359 48 64));
      v_8365 <- evaluateAddress v_2764;
      v_8366 <- load v_8365 2;
      setRegister rdx (concat (extract v_8361 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int16 v_8364 v_8366));
      setRegister rax (concat (extract v_8359 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int16 v_8364 v_8366));
      setRegister of undef;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end
