def pinsrw : instruction :=
  definst "pinsrw" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      v_4 <- eval (extract (shl (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend imm_0 8 8) 5 8)) (expression.bv_nat 128 4)) 0 128);
      v_5 <- eval (shl (expression.bv_nat 128 65535) v_4);
      v_6 <- evaluateAddress mem_1;
      v_7 <- load v_6 2;
      setRegister (lhs.of_reg xmm_2) (bv_or (bv_and v_3 (bv_xor (extract v_5 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 112 0) v_7) v_4) v_5) 0 128));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r32_1 : reg (bv 32)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      v_4 <- eval (extract (shl (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend imm_0 8 8) 5 8)) (expression.bv_nat 128 4)) 0 128);
      v_5 <- eval (shl (expression.bv_nat 128 65535) v_4);
      v_6 <- getRegister (lhs.of_reg r32_1);
      setRegister (lhs.of_reg xmm_2) (bv_or (bv_and v_3 (bv_xor (extract v_5 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 96 0) v_6) v_4) v_5) 0 128));
      pure ()
    pat_end
