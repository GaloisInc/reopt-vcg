def divl1 : instruction :=
  definst "divl" $ do
    pattern fun (v_2782 : reg (bv 32)) => do
      v_4502 <- getRegister rdx;
      v_4504 <- getRegister rax;
      v_4506 <- eval (concat (extract v_4502 32 64) (extract v_4504 32 64));
      v_4507 <- getRegister v_2782;
      setRegister edx (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int32 v_4506 v_4507);
      setRegister eax (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int32 v_4506 v_4507);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2778 : Mem) => do
      v_8035 <- getRegister rdx;
      v_8037 <- getRegister rax;
      v_8039 <- eval (concat (extract v_8035 32 64) (extract v_8037 32 64));
      v_8040 <- evaluateAddress v_2778;
      v_8041 <- load v_8040 4;
      setRegister edx (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int32 v_8039 v_8041);
      setRegister eax (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int32 v_8039 v_8041);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
