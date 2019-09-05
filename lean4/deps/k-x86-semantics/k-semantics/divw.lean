def divw1 : instruction :=
  definst "divw" $ do
    pattern fun (v_2832 : reg (bv 16)) => do
      v_4622 <- getRegister rax;
      v_4624 <- getRegister rdx;
      v_4627 <- eval (concat (extract v_4624 48 64) (extract v_4622 48 64));
      v_4628 <- getRegister v_2832;
      setRegister rdx (concat (extract v_4624 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int16 v_4627 v_4628));
      setRegister rax (concat (extract v_4622 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int16 v_4627 v_4628));
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2828 : Mem) => do
      v_8137 <- getRegister rax;
      v_8139 <- getRegister rdx;
      v_8142 <- eval (concat (extract v_8139 48 64) (extract v_8137 48 64));
      v_8143 <- evaluateAddress v_2828;
      v_8144 <- load v_8143 2;
      setRegister rdx (concat (extract v_8139 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX div_remainder_int16 v_8142 v_8144));
      setRegister rax (concat (extract v_8137 0 48) (_(_,_)_MINT-WRAPPER-SYNTAX div_quotient_int16 v_8142 v_8144));
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
