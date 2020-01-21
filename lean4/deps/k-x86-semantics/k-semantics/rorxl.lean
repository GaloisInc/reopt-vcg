def rorxl : instruction :=
  definst "rorxl" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (r32_2 : reg (bv 32)) => do
      v_3 <- evaluateAddress mem_1;
      v_4 <- load v_3 4;
      v_5 <- eval (bv_and (concat (expression.bv_nat 24 0) (handleImmediateWithSignExtend imm_0 8 8)) (expression.bv_nat 32 31));
      setRegister (lhs.of_reg r32_2) (bv_or (lshr v_4 v_5) (extract (shl v_4 (sub (expression.bv_nat 32 32) v_5)) 0 32));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r32_1 : reg (bv 32)) (r32_2 : reg (bv 32)) => do
      v_3 <- getRegister (lhs.of_reg r32_1);
      v_4 <- eval (bv_and (concat (expression.bv_nat 24 0) (handleImmediateWithSignExtend imm_0 8 8)) (expression.bv_nat 32 31));
      setRegister (lhs.of_reg r32_2) (bv_or (lshr v_3 v_4) (extract (shl v_3 (sub (expression.bv_nat 32 32) v_4)) 0 32));
      pure ()
    pat_end
