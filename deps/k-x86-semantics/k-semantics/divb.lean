def divb : instruction :=
  definst "divb" $ do
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- getRegister rax;
      let (v_2 : expression (bv 48)) <- eval (extract v_1 0 48);
      let (v_3 : expression (bv 16)) <- eval (extract v_1 48 64);
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 1;
      let v_6 <- eval (concat v_2 (/- (_,_) -/  div_remainder_int8 v_3 v_5));
      let v_7 <- eval (concat v_6 (/- (_,_) -/  div_quotient_int8 v_3 v_5));
      setRegister rax v_7;
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action;
    instr_pat $ fun (rh_0 : reg (bv 8)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister rax;
      let (v_2 : expression (bv 48)) <- eval (extract v_1 0 48);
      let (v_3 : expression (bv 16)) <- eval (extract v_1 48 64);
      let v_4 <- getRegister (lhs.of_reg rh_0);
      let v_5 <- eval (concat v_2 (/- (_,_) -/  div_remainder_int8 v_3 v_4));
      let v_6 <- eval (concat v_5 (/- (_,_) -/  div_quotient_int8 v_3 v_4));
      setRegister rax v_6;
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action
