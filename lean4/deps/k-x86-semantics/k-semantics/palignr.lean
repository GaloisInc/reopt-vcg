def palignr : instruction :=
  definst "palignr" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      v_4 <- evaluateAddress mem_1;
      v_5 <- load v_4 16;
      (v_6 : expression (bv 256)) <- eval (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend imm_0 8 8)) (expression.bv_nat 256 3)) 0 256);
      (v_7 : expression (bv 128)) <- eval (extract (lshr (concat v_3 v_5) v_6) 128 256);
      setRegister (lhs.of_reg xmm_2) v_7;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      (v_5 : expression (bv 256)) <- eval (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend imm_0 8 8)) (expression.bv_nat 256 3)) 0 256);
      (v_6 : expression (bv 128)) <- eval (extract (lshr (concat v_3 v_4) v_5) 128 256);
      setRegister (lhs.of_reg xmm_2) v_6;
      pure ()
    pat_end
