def idivb : instruction :=
  definst "idivb" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- getRegister rax;
      v_2 <- eval (extract v_1 48 64);
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 1;
      setRegister rax (concat (concat (extract v_1 0 48) (/- (_,_) -/  idiv_remainder_int8 v_2 v_4)) (/- (_,_) -/  idiv_quotient_int8 v_2 v_4));
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (rh_0 : reg (bv 8)) => do
      v_1 <- getRegister rax;
      v_2 <- eval (extract v_1 48 64);
      v_3 <- getRegister (lhs.of_reg rh_0);
      setRegister rax (concat (concat (extract v_1 0 48) (/- (_,_) -/  idiv_remainder_int8 v_2 v_3)) (/- (_,_) -/  idiv_quotient_int8 v_2 v_3));
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
