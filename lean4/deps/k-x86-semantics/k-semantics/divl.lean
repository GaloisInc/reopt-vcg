def divl1 : instruction :=
  definst "divl" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- getRegister rdx;
      v_2 <- getRegister rax;
      v_3 <- eval (concat (extract v_1 32 64) (extract v_2 32 64));
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 4;
      setRegister eax (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int32 v_3 v_5);
      setRegister edx (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int32 v_3 v_5);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) => do
      v_1 <- getRegister rdx;
      v_2 <- getRegister rax;
      v_3 <- eval (concat (extract v_1 32 64) (extract v_2 32 64));
      v_4 <- getRegister r32_0;
      setRegister eax (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int32 v_3 v_4);
      setRegister edx (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int32 v_3 v_4);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
