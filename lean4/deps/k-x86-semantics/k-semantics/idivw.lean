def idivw1 : instruction :=
  definst "idivw" $ do
    pattern fun (v_2887 : reg (bv 16)) => do
      v_5297 <- getRegister rax;
      v_5299 <- getRegister rdx;
      v_5302 <- eval (concat (extract v_5299 48 64) (extract v_5297 48 64));
      v_5303 <- getRegister v_2887;
      setRegister rdx (concat (extract v_5299 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int16 v_5302 v_5303));
      setRegister rax (concat (extract v_5297 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int16 v_5302 v_5303));
      setRegister of undef;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end;
    pattern fun (v_2882 : Mem) => do
      v_9247 <- getRegister rax;
      v_9249 <- getRegister rdx;
      v_9252 <- eval (concat (extract v_9249 48 64) (extract v_9247 48 64));
      v_9253 <- evaluateAddress v_2882;
      v_9254 <- load v_9253 2;
      setRegister rdx (concat (extract v_9249 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_remainder_int16 v_9252 v_9254));
      setRegister rax (concat (extract v_9247 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX idiv_quotient_int16 v_9252 v_9254));
      setRegister of undef;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf undef;
      pure ()
    pat_end
