def idivl1 : instruction :=
  definst "idivl" $ do
    pattern fun (v_2872 : reg (bv 32)) => do
      v_5261 <- getRegister rdx;
      v_5263 <- getRegister rax;
      v_5265 <- eval (concat (extract v_5261 32 64) (extract v_5263 32 64));
      v_5266 <- getRegister v_2872;
      setRegister edx (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int32 v_5265 v_5266);
      setRegister eax (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int32 v_5265 v_5266);
      setRegister of undef;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end;
    pattern fun (v_2868 : Mem) => do
      v_9215 <- getRegister rdx;
      v_9217 <- getRegister rax;
      v_9219 <- eval (concat (extract v_9215 32 64) (extract v_9217 32 64));
      v_9220 <- evaluateAddress v_2868;
      v_9221 <- load v_9220 4;
      setRegister edx (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int32 v_9219 v_9221);
      setRegister eax (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int32 v_9219 v_9221);
      setRegister of undef;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end
