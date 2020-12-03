def psrldq : instruction :=
  definst "psrldq" $ do
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_4 <- eval (concat (expression.bv_nat 120 0) v_3);
      let (v_5 : expression (bv 128)) <- eval (extract (shl (mux (ugt v_3 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) v_4) (expression.bv_nat 128 3)) 0 128);
      setRegister (lhs.of_reg xmm_1) (lshr v_2 v_5);
      pure ()
     action
