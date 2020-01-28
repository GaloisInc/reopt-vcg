def idivw : instruction :=
  definst "idivw" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- getRegister rdx;
      v_2 <- getRegister rax;
      v_3 <- eval (concat (extract v_1 48 64) (extract v_2 48 64));
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 2;
      setRegister rax (concat (extract v_2 0 48) (/- (_,_) -/  idiv_quotient_int16 v_3 v_5));
      setRegister rdx (concat (extract v_1 0 48) (/- (_,_) -/  idiv_remainder_int16 v_3 v_5));
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
      v_2 <- getRegister rax;
      v_3 <- eval (concat (extract v_1 48 64) (extract v_2 48 64));
      v_4 <- getRegister (lhs.of_reg r16_0);
      setRegister rax (concat (extract v_2 0 48) (/- (_,_) -/  idiv_quotient_int16 v_3 v_4));
      setRegister rdx (concat (extract v_1 0 48) (/- (_,_) -/  idiv_remainder_int16 v_3 v_4));
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
