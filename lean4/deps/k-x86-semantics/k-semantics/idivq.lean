def idivq1 : instruction :=
  definst "idivq" $ do
    pattern fun (v_2867 : reg (bv 64)) => do
      v_4950 <- getRegister rdx;
      v_4951 <- getRegister rax;
      v_4952 <- eval (concat v_4950 v_4951);
      v_4953 <- getRegister v_2867;
      setRegister rdx (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int64 v_4952 v_4953);
      setRegister rax (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int64 v_4952 v_4953);
      setRegister of undef;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end;
    pattern fun (v_2864 : Mem) => do
      v_8612 <- getRegister rdx;
      v_8613 <- getRegister rax;
      v_8614 <- eval (concat v_8612 v_8613);
      v_8615 <- evaluateAddress v_2864;
      v_8616 <- load v_8615 8;
      setRegister rdx (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int64 v_8614 v_8616);
      setRegister rax (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int64 v_8614 v_8616);
      setRegister of undef;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end
