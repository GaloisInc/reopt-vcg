def pinsrq : instruction :=
  definst "pinsrq" $ do
    instr_pat $ fun (imm_0 : imm int) (r64_1 : reg (bv 64)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_2);
      let (v_4 : expression (bv 1)) <- eval (extract (handleImmediateWithSignExtend imm_0 8 8) 7 8);
      let v_5 <- eval (concat (expression.bv_nat 127 0) v_4);
      let (v_6 : expression (bv 128)) <- eval (extract (shl v_5 (expression.bv_nat 128 6)) 0 128);
      let v_7 <- eval (shl (expression.bv_nat 128 18446744073709551615) v_6);
      let (v_8 : expression (bv 128)) <- eval (extract v_7 0 128);
      let v_9 <- getRegister (lhs.of_reg r64_1);
      let v_10 <- eval (concat (expression.bv_nat 64 0) v_9);
      let (v_11 : expression (bv 128)) <- eval (extract (bv_and (shl v_10 v_6) v_7) 0 128);
      setRegister (lhs.of_reg xmm_2) (bv_or (bv_and v_3 (bv_xor v_8 (expression.bv_nat 128 340282366920938463463374607431768211455))) v_11);
      pure ()
     action
