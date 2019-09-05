def idivb1 : instruction :=
  definst "idivb" $ do
    pattern fun (v_2917 : reg (bv 8)) => do
      v_4890 <- getRegister rax;
      v_4892 <- eval (extract v_4890 48 64);
      v_4893 <- getRegister v_2917;
      setRegister rax (concat (concat (extract v_4890 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int8 v_4892 v_4893)) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int8 v_4892 v_4893));
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2910 : Mem) => do
      v_8345 <- getRegister rax;
      v_8347 <- eval (extract v_8345 48 64);
      v_8348 <- evaluateAddress v_2910;
      v_8349 <- load v_8348 1;
      setRegister rax (concat (concat (extract v_8345 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int8 v_8347 v_8349)) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int8 v_8347 v_8349));
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
