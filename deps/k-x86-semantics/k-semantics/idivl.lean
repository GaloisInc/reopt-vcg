def idivl : instruction :=
  definst "idivl" $ do
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- getRegister rdx;
      let (v_2 : expression (bv 32)) <- eval (extract v_1 32 64);
      let v_3 <- getRegister rax;
      let (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_5 <- eval (concat v_2 v_4);
      let v_6 <- evaluateAddress mem_0;
      let v_7 <- load v_6 4;
      setRegister eax (/- (_,_) -/  idiv_quotient_int32 v_5 v_7);
      setRegister edx (/- (_,_) -/  idiv_remainder_int32 v_5 v_7);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister rdx;
      let (v_2 : expression (bv 32)) <- eval (extract v_1 32 64);
      let v_3 <- getRegister rax;
      let (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_5 <- eval (concat v_2 v_4);
      let v_6 <- getRegister (lhs.of_reg r32_0);
      setRegister eax (/- (_,_) -/  idiv_quotient_int32 v_5 v_6);
      setRegister edx (/- (_,_) -/  idiv_remainder_int32 v_5 v_6);
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action
