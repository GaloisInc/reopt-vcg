def vucomiss : instruction :=
  definst "vucomiss" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 96 128);
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 4;
      let v_6 <- eval (/- (_,_) -/  comiss v_3 v_5);
      let v_7 <- eval (eq v_6 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_7 (eq v_6 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_7;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_7 (eq v_6 (expression.bv_nat 2 3)));
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 96 128);
      let v_4 <- getRegister (lhs.of_reg xmm_0);
      let (v_5 : expression (bv 32)) <- eval (extract v_4 96 128);
      let v_6 <- eval (/- (_,_) -/  comiss v_3 v_5);
      let v_7 <- eval (eq v_6 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_7 (eq v_6 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_7;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_7 (eq v_6 (expression.bv_nat 2 3)));
      pure ()
     action
