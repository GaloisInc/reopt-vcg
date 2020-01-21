def rorxq : instruction :=
  definst "rorxq" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (r64_2 : reg (bv 64)) => do
      v_3 <- evaluateAddress mem_1;
      v_4 <- load v_3 8;
      v_5 <- eval (bv_and (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend imm_0 8 8)) (expression.bv_nat 64 63));
      setRegister (lhs.of_reg r64_2) (bv_or (lshr v_4 v_5) (extract (shl v_4 (sub (expression.bv_nat 64 64) v_5)) 0 64));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r64_1 : reg (bv 64)) (r64_2 : reg (bv 64)) => do
      v_3 <- getRegister (lhs.of_reg r64_1);
      v_4 <- eval (bv_and (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend imm_0 8 8)) (expression.bv_nat 64 63));
      setRegister (lhs.of_reg r64_2) (bv_or (lshr v_3 v_4) (extract (shl v_3 (sub (expression.bv_nat 64 64) v_4)) 0 64));
      pure ()
    pat_end
