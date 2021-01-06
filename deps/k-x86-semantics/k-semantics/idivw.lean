def idivw : instruction :=
  definst "idivw" $ do
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- getRegister rdx;
      let (v_2 : expression (bv 48)) <- eval (extract v_1 0 48);
      let (v_3 : expression (bv 16)) <- eval (extract v_1 48 64);
      let v_4 <- getRegister rax;
      let (v_5 : expression (bv 16)) <- eval (extract v_4 48 64);
      let v_6 <- eval (concat v_3 v_5);
      let v_7 <- evaluateAddress mem_0;
      let v_8 <- load v_7 2;
      let v_9 <- eval (concat v_2 (/- (_,_) -/  idiv_remainder_int16 v_6 v_8));
      let (v_10 : expression (bv 48)) <- eval (extract v_4 0 48);
      let v_11 <- eval (concat v_10 (/- (_,_) -/  idiv_quotient_int16 v_6 v_8));
      setRegister rax v_11;
      setRegister rdx v_9;
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action;
    instr_pat $ fun (r16_0 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister rdx;
      let (v_2 : expression (bv 48)) <- eval (extract v_1 0 48);
      let (v_3 : expression (bv 16)) <- eval (extract v_1 48 64);
      let v_4 <- getRegister rax;
      let (v_5 : expression (bv 16)) <- eval (extract v_4 48 64);
      let v_6 <- eval (concat v_3 v_5);
      let v_7 <- getRegister (lhs.of_reg r16_0);
      let v_8 <- eval (concat v_2 (/- (_,_) -/  idiv_remainder_int16 v_6 v_7));
      let (v_9 : expression (bv 48)) <- eval (extract v_4 0 48);
      let v_10 <- eval (concat v_9 (/- (_,_) -/  idiv_quotient_int16 v_6 v_7));
      setRegister rax v_10;
      setRegister rdx v_8;
      setRegister af undef;
      setRegister cf undef;
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action
