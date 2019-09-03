def divl1 : instruction :=
  definst "divl" $ do
    pattern fun (v_2717 : reg (bv 32)) => do
      v_4509 <- getRegister rdx;
      v_4511 <- getRegister rax;
      v_4513 <- eval (concat (extract v_4509 32 64) (extract v_4511 32 64));
      v_4514 <- getRegister v_2717;
      setRegister edx (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int32 v_4513 v_4514);
      setRegister eax (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int32 v_4513 v_4514);
      setRegister of undef;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end;
    pattern fun (v_2714 : Mem) => do
      v_8257 <- getRegister rdx;
      v_8259 <- getRegister rax;
      v_8261 <- eval (concat (extract v_8257 32 64) (extract v_8259 32 64));
      v_8262 <- evaluateAddress v_2714;
      v_8263 <- load v_8262 4;
      setRegister edx (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int32 v_8261 v_8263);
      setRegister eax (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int32 v_8261 v_8263);
      setRegister of undef;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end
