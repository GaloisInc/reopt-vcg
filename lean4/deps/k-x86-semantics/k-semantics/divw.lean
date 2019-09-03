def divw1 : instruction :=
  definst "divw" $ do
    pattern fun (v_2780 : reg (bv 16)) => do
      v_4745 <- getRegister rax;
      v_4747 <- getRegister rdx;
      v_4750 <- eval (concat (extract v_4747 48 64) (extract v_4745 48 64));
      v_4751 <- getRegister v_2780;
      setRegister rdx (concat (extract v_4747 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int16 v_4750 v_4751));
      setRegister rax (concat (extract v_4745 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int16 v_4750 v_4751));
      setRegister of undef;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end;
    pattern fun (v_2775 : Mem) => do
      v_8763 <- getRegister rax;
      v_8765 <- getRegister rdx;
      v_8768 <- eval (concat (extract v_8765 48 64) (extract v_8763 48 64));
      v_8769 <- evaluateAddress v_2775;
      v_8770 <- load v_8769 2;
      setRegister rdx (concat (extract v_8765 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int16 v_8768 v_8770));
      setRegister rax (concat (extract v_8763 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int16 v_8768 v_8770));
      setRegister of undef;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end
