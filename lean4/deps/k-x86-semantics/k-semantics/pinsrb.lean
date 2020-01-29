def pinsrb : instruction :=
  definst "pinsrb" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      (v_4 : expression (bv 4)) <- eval (extract (handleImmediateWithSignExtend imm_0 8 8) 4 8);
      (v_5 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 124 0) v_4) (expression.bv_nat 128 3)) 0 128);
      v_6 <- eval (shl (expression.bv_nat 128 255) v_5);
      (v_7 : expression (bv 128)) <- eval (extract v_6 0 128);
      v_8 <- evaluateAddress mem_1;
      v_9 <- load v_8 1;
      (v_10 : expression (bv 128)) <- eval (extract (bv_and (shl (concat (expression.bv_nat 120 0) v_9) v_5) v_6) 0 128);
      setRegister (lhs.of_reg xmm_2) (bv_or (bv_and v_3 (bv_xor v_7 (expression.bv_nat 128 340282366920938463463374607431768211455))) v_10);
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r32_1 : reg (bv 32)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      (v_4 : expression (bv 4)) <- eval (extract (handleImmediateWithSignExtend imm_0 8 8) 4 8);
      (v_5 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 124 0) v_4) (expression.bv_nat 128 3)) 0 128);
      v_6 <- eval (shl (expression.bv_nat 128 255) v_5);
      (v_7 : expression (bv 128)) <- eval (extract v_6 0 128);
      v_8 <- getRegister (lhs.of_reg r32_1);
      (v_9 : expression (bv 128)) <- eval (extract (bv_and (shl (concat (expression.bv_nat 96 0) v_8) v_5) v_6) 0 128);
      setRegister (lhs.of_reg xmm_2) (bv_or (bv_and v_3 (bv_xor v_7 (expression.bv_nat 128 340282366920938463463374607431768211455))) v_9);
      pure ()
    pat_end
