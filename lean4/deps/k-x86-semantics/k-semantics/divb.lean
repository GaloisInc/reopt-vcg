def divb1 : instruction :=
  definst "divb" $ do
    pattern fun (v_2802 : reg (bv 8)) => do
      v_4505 <- getRegister rax;
      v_4507 <- eval (extract v_4505 48 64);
      v_4508 <- getRegister v_2802;
      setRegister rax (concat (concat (extract v_4505 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int8 v_4507 v_4508)) (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int8 v_4507 v_4508));
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2794 : Mem) => do
      v_8029 <- getRegister rax;
      v_8031 <- eval (extract v_8029 48 64);
      v_8032 <- evaluateAddress v_2794;
      v_8033 <- load v_8032 1;
      setRegister rax (concat (concat (extract v_8029 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int8 v_8031 v_8033)) (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int8 v_8031 v_8033));
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
