def idivw1 : instruction :=
  definst "idivw" $ do
    pattern fun (v_2874 : reg (bv 16)) => do
      v_4967 <- getRegister rax;
      v_4969 <- getRegister rdx;
      v_4972 <- eval (concat (extract v_4969 48 64) (extract v_4967 48 64));
      v_4973 <- getRegister v_2874;
      setRegister rdx (concat (extract v_4969 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int16 v_4972 v_4973));
      setRegister rax (concat (extract v_4967 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int16 v_4972 v_4973));
      setRegister of undef;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end;
    pattern fun (v_2871 : Mem) => do
      v_8627 <- getRegister rax;
      v_8629 <- getRegister rdx;
      v_8632 <- eval (concat (extract v_8629 48 64) (extract v_8627 48 64));
      v_8633 <- evaluateAddress v_2871;
      v_8634 <- load v_8633 2;
      setRegister rdx (concat (extract v_8629 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int16 v_8632 v_8634));
      setRegister rax (concat (extract v_8627 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int16 v_8632 v_8634));
      setRegister of undef;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end
