def vpinsrd : instruction :=
  definst "vpinsrd" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister (lhs.of_reg xmm_2);
      (v_5 : expression (bv 2)) <- eval (extract (handleImmediateWithSignExtend imm_0 8 8) 6 8);
      (v_6 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 126 0) v_5) (expression.bv_nat 128 5)) 0 128);
      v_7 <- eval (shl (expression.bv_nat 128 4294967295) v_6);
      (v_8 : expression (bv 128)) <- eval (extract v_7 0 128);
      v_9 <- evaluateAddress mem_1;
      v_10 <- load v_9 4;
      (v_11 : expression (bv 128)) <- eval (extract (bv_and (shl (concat (expression.bv_nat 96 0) v_10) v_6) v_7) 0 128);
      setRegister (lhs.of_reg xmm_3) (bv_or (bv_and v_4 (bv_xor v_8 (expression.bv_nat 128 340282366920938463463374607431768211455))) v_11);
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r32_1 : reg (bv 32)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister (lhs.of_reg xmm_2);
      (v_5 : expression (bv 2)) <- eval (extract (handleImmediateWithSignExtend imm_0 8 8) 6 8);
      (v_6 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 126 0) v_5) (expression.bv_nat 128 5)) 0 128);
      v_7 <- eval (shl (expression.bv_nat 128 4294967295) v_6);
      (v_8 : expression (bv 128)) <- eval (extract v_7 0 128);
      v_9 <- getRegister (lhs.of_reg r32_1);
      (v_10 : expression (bv 128)) <- eval (extract (bv_and (shl (concat (expression.bv_nat 96 0) v_9) v_6) v_7) 0 128);
      setRegister (lhs.of_reg xmm_3) (bv_or (bv_and v_4 (bv_xor v_8 (expression.bv_nat 128 340282366920938463463374607431768211455))) v_10);
      pure ()
    pat_end
