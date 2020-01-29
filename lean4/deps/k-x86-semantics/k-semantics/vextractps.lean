def vextractps : instruction :=
  definst "vextractps" $ do
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (mem_2 : Mem) => do
      v_3 <- evaluateAddress mem_2;
      v_4 <- getRegister (lhs.of_reg xmm_1);
      (v_5 : expression (bv 2)) <- eval (extract (handleImmediateWithSignExtend imm_0 8 8) 6 8);
      (v_6 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 126 0) v_5) (expression.bv_nat 128 5)) 0 128);
      (v_7 : expression (bv 32)) <- eval (extract (lshr v_4 v_6) 96 128);
      store v_3 v_7 4;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (r32_2 : reg (bv 32)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 2)) <- eval (extract (handleImmediateWithSignExtend imm_0 8 8) 6 8);
      (v_5 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 126 0) v_4) (expression.bv_nat 128 5)) 0 128);
      (v_6 : expression (bv 32)) <- eval (extract (lshr v_3 v_5) 96 128);
      setRegister (lhs.of_reg r32_2) v_6;
      pure ()
    pat_end
