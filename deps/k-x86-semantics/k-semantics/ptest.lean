def ptest : instruction :=
  definst "ptest" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 16;
      setRegister af bit_zero;
      setRegister cf (eq (bv_and (bv_xor v_2 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_4) (expression.bv_nat 128 0));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (zeroFlag (bv_and v_2 v_4));
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let v_3 <- getRegister (lhs.of_reg xmm_0);
      setRegister af bit_zero;
      setRegister cf (eq (bv_and (bv_xor v_2 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_3) (expression.bv_nat 128 0));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (zeroFlag (bv_and v_2 v_3));
      pure ()
     action
