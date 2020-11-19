def vpextrq : instruction :=
  definst "vpextrq" $ do
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (mem_2 : Mem) => do
      v_3 <- evaluateAddress mem_2;
      v_4 <- getRegister (lhs.of_reg xmm_1);
      (v_5 : expression (bv 1)) <- eval (extract (handleImmediateWithSignExtend imm_0 8 8) 7 8);
      (v_6 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 127 0) v_5) (expression.bv_nat 128 6)) 0 128);
      (v_7 : expression (bv 64)) <- eval (extract (lshr v_4 v_6) 64 128);
      store v_3 v_7 8;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (r64_2 : reg (bv 64)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 1)) <- eval (extract (handleImmediateWithSignExtend imm_0 8 8) 7 8);
      (v_5 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 127 0) v_4) (expression.bv_nat 128 6)) 0 128);
      (v_6 : expression (bv 64)) <- eval (extract (lshr v_3 v_5) 64 128);
      setRegister (lhs.of_reg r64_2) v_6;
      pure ()
    pat_end
