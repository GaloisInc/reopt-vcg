def vpinsrb : instruction :=
  definst "vpinsrb" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_4 <- getRegister (lhs.of_reg xmm_2);
      let (v_5 : expression (bv 4)) <- eval (extract (handleImmediateWithSignExtend imm_0 8 8) 4 8);
      let v_6 <- eval (concat (expression.bv_nat 124 0) v_5);
      let (v_7 : expression (bv 128)) <- eval (extract (shl v_6 (expression.bv_nat 128 3)) 0 128);
      let v_8 <- eval (shl (expression.bv_nat 128 255) v_7);
      let (v_9 : expression (bv 128)) <- eval (extract v_8 0 128);
      let v_10 <- evaluateAddress mem_1;
      let v_11 <- load v_10 1;
      let v_12 <- eval (concat (expression.bv_nat 120 0) v_11);
      let (v_13 : expression (bv 128)) <- eval (extract (bv_and (shl v_12 v_7) v_8) 0 128);
      setRegister (lhs.of_reg xmm_3) (bv_or (bv_and v_4 (bv_xor v_9 (expression.bv_nat 128 340282366920938463463374607431768211455))) v_13);
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (r32_1 : reg (bv 32)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_4 <- getRegister (lhs.of_reg xmm_2);
      let (v_5 : expression (bv 4)) <- eval (extract (handleImmediateWithSignExtend imm_0 8 8) 4 8);
      let v_6 <- eval (concat (expression.bv_nat 124 0) v_5);
      let (v_7 : expression (bv 128)) <- eval (extract (shl v_6 (expression.bv_nat 128 3)) 0 128);
      let v_8 <- eval (shl (expression.bv_nat 128 255) v_7);
      let (v_9 : expression (bv 128)) <- eval (extract v_8 0 128);
      let v_10 <- getRegister (lhs.of_reg r32_1);
      let v_11 <- eval (concat (expression.bv_nat 96 0) v_10);
      let (v_12 : expression (bv 128)) <- eval (extract (bv_and (shl v_11 v_7) v_8) 0 128);
      setRegister (lhs.of_reg xmm_3) (bv_or (bv_and v_4 (bv_xor v_9 (expression.bv_nat 128 340282366920938463463374607431768211455))) v_12);
      pure ()
     action
