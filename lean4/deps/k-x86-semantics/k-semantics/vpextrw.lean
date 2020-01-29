def vpextrw : instruction :=
  definst "vpextrw" $ do
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (mem_2 : Mem) => do
      v_3 <- evaluateAddress mem_2;
      v_4 <- getRegister (lhs.of_reg xmm_1);
      (v_5 : expression (bv 3)) <- eval (extract (handleImmediateWithSignExtend imm_0 8 8) 5 8);
      (v_6 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 125 0) v_5) (expression.bv_nat 128 4)) 0 128);
      (v_7 : expression (bv 16)) <- eval (extract (lshr v_4 v_6) 112 128);
      store v_3 v_7 2;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (r32_2 : reg (bv 32)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 3)) <- eval (extract (handleImmediateWithSignExtend imm_0 8 8) 5 8);
      (v_5 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 125 0) v_4) (expression.bv_nat 128 4)) 0 128);
      (v_6 : expression (bv 16)) <- eval (extract (lshr v_3 v_5) 112 128);
      setRegister (lhs.of_reg r32_2) (concat (expression.bv_nat 16 0) v_6);
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (r64_2 : reg (bv 64)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 3)) <- eval (extract (handleImmediateWithSignExtend imm_0 8 8) 5 8);
      (v_5 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 125 0) v_4) (expression.bv_nat 128 4)) 0 128);
      (v_6 : expression (bv 16)) <- eval (extract (lshr v_3 v_5) 112 128);
      setRegister (lhs.of_reg r64_2) (concat (expression.bv_nat 48 0) v_6);
      pure ()
    pat_end
