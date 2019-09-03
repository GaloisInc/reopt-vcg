def divl1 : instruction :=
  definst "divl" $ do
    pattern fun (v_2729 : reg (bv 32)) => do
      v_4529 <- getRegister rdx;
      v_4531 <- getRegister rax;
      v_4533 <- eval (concat (extract v_4529 32 64) (extract v_4531 32 64));
      v_4534 <- getRegister v_2729;
      setRegister edx (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int32 v_4533 v_4534);
      setRegister eax (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int32 v_4533 v_4534);
      setRegister of undef;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end;
    pattern fun (v_2725 : Mem) => do
      v_8565 <- getRegister rdx;
      v_8567 <- getRegister rax;
      v_8569 <- eval (concat (extract v_8565 32 64) (extract v_8567 32 64));
      v_8570 <- evaluateAddress v_2725;
      v_8571 <- load v_8570 4;
      setRegister edx (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int32 v_8569 v_8571);
      setRegister eax (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int32 v_8569 v_8571);
      setRegister of undef;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end
