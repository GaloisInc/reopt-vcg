def idivq : instruction :=
  definst "idivq" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- getRegister rdx;
      v_2 <- getRegister rax;
      v_3 <- eval (concat v_1 v_2);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 8;
      setRegister rax (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int64 v_3 v_5);
      setRegister rdx (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int64 v_3 v_5);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) => do
      v_1 <- getRegister rdx;
      v_2 <- getRegister rax;
      v_3 <- eval (concat v_1 v_2);
      v_4 <- getRegister (lhs.of_reg r64_0);
      setRegister rax (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int64 v_3 v_4);
      setRegister rdx (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int64 v_3 v_4);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
