def idivl : instruction :=
  definst "idivl" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- getRegister rdx;
      v_2 <- getRegister rax;
      v_3 <- eval (concat (extract v_1 32 64) (extract v_2 32 64));
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 4;
      setRegister eax (/- (_,_) -/  idiv_quotient_int32 v_3 v_5);
      setRegister edx (/- (_,_) -/  idiv_remainder_int32 v_3 v_5);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) => do
      v_1 <- getRegister rdx;
      v_2 <- getRegister rax;
      v_3 <- eval (concat (extract v_1 32 64) (extract v_2 32 64));
      v_4 <- getRegister (lhs.of_reg r32_0);
      setRegister eax (/- (_,_) -/  idiv_quotient_int32 v_3 v_4);
      setRegister edx (/- (_,_) -/  idiv_remainder_int32 v_3 v_4);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
