def divl1 : instruction :=
  definst "divl" $ do
    pattern fun (v_2808 : reg (bv 32)) => do
      v_4523 <- getRegister rdx;
      v_4525 <- getRegister rax;
      v_4527 <- eval (concat (extract v_4523 32 64) (extract v_4525 32 64));
      v_4528 <- getRegister v_2808;
      setRegister eax (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int32 v_4527 v_4528);
      setRegister edx (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int32 v_4527 v_4528);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2805 : Mem) => do
      v_8045 <- getRegister rdx;
      v_8047 <- getRegister rax;
      v_8049 <- eval (concat (extract v_8045 32 64) (extract v_8047 32 64));
      v_8050 <- evaluateAddress v_2805;
      v_8051 <- load v_8050 4;
      setRegister eax (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int32 v_8049 v_8051);
      setRegister edx (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int32 v_8049 v_8051);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
