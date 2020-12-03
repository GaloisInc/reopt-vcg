def divq : instruction :=
  definst "divq" $ do
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- getRegister rdx;
      let v_2 <- getRegister rax;
      let v_3 <- eval (concat v_1 v_2);
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 8;
      setRegister rax (/- (_,_) -/  div_quotient_int64 v_3 v_5);
      setRegister rdx (/- (_,_) -/  div_remainder_int64 v_3 v_5);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister rdx;
      let v_2 <- getRegister rax;
      let v_3 <- eval (concat v_1 v_2);
      let v_4 <- getRegister (lhs.of_reg r64_0);
      setRegister rax (/- (_,_) -/  div_quotient_int64 v_3 v_4);
      setRegister rdx (/- (_,_) -/  div_remainder_int64 v_3 v_4);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action
