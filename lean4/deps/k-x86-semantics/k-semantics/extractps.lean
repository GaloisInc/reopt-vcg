def extractps : instruction :=
  definst "extractps" $ do
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (mem_2 : Mem) => do
      v_3 <- evaluateAddress mem_2;
      v_4 <- getRegister (lhs.of_reg xmm_1);
      store v_3 (extract (lshr v_4 (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend imm_0 8 8) 6 8)) (expression.bv_nat 128 5)) 0 128)) 96 128) 4;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (r32_2 : reg (bv 32)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      setRegister (lhs.of_reg r32_2) (extract (lshr v_3 (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend imm_0 8 8) 6 8)) (expression.bv_nat 128 5)) 0 128)) 96 128);
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (r64_2 : reg (bv 64)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      setRegister (lhs.of_reg r64_2) (concat (expression.bv_nat 32 0) (extract (lshr v_3 (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend imm_0 8 8) 6 8)) (expression.bv_nat 128 5)) 0 128)) 96 128));
      pure ()
    pat_end
