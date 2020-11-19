def idivw : instruction :=
  definst "idivw" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- getRegister rdx;
      (v_2 : expression (bv 48)) <- eval (extract v_1 0 48);
      (v_3 : expression (bv 16)) <- eval (extract v_1 48 64);
      v_4 <- getRegister rax;
      (v_5 : expression (bv 16)) <- eval (extract v_4 48 64);
      v_6 <- eval (concat v_3 v_5);
      v_7 <- evaluateAddress mem_0;
      v_8 <- load v_7 2;
      (v_9 : expression (bv 48)) <- eval (extract v_4 0 48);
      setRegister rax (concat v_9 (/- (_,_) -/  idiv_quotient_int16 v_6 v_8));
      setRegister rdx (concat v_2 (/- (_,_) -/  idiv_remainder_int16 v_6 v_8));
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) => do
      v_1 <- getRegister rdx;
      (v_2 : expression (bv 48)) <- eval (extract v_1 0 48);
      (v_3 : expression (bv 16)) <- eval (extract v_1 48 64);
      v_4 <- getRegister rax;
      (v_5 : expression (bv 16)) <- eval (extract v_4 48 64);
      v_6 <- eval (concat v_3 v_5);
      v_7 <- getRegister (lhs.of_reg r16_0);
      (v_8 : expression (bv 48)) <- eval (extract v_4 0 48);
      setRegister rax (concat v_8 (/- (_,_) -/  idiv_quotient_int16 v_6 v_7));
      setRegister rdx (concat v_2 (/- (_,_) -/  idiv_remainder_int16 v_6 v_7));
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
