def divw1 : instruction :=
  definst "divw" $ do
    pattern fun (v_2858 : reg (bv 16)) => do
      v_4643 <- getRegister rdx;
      v_4646 <- getRegister rax;
      v_4648 <- eval (concat (extract v_4643 48 64) (extract v_4646 48 64));
      v_4649 <- getRegister v_2858;
      setRegister rax (concat (extract v_4646 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int16 v_4648 v_4649));
      setRegister rdx (concat (extract v_4643 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int16 v_4648 v_4649));
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2855 : Mem) => do
      v_8147 <- getRegister rdx;
      v_8150 <- getRegister rax;
      v_8152 <- eval (concat (extract v_8147 48 64) (extract v_8150 48 64));
      v_8153 <- evaluateAddress v_2855;
      v_8154 <- load v_8153 2;
      setRegister rax (concat (extract v_8150 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int16 v_8152 v_8154));
      setRegister rdx (concat (extract v_8147 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int16 v_8152 v_8154));
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
