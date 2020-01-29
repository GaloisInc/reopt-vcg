def pinsrq : instruction :=
  definst "pinsrq" $ do
    pattern fun (imm_0 : imm int) (r64_1 : reg (bv 64)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      (v_4 : expression (bv 1)) <- eval (extract (handleImmediateWithSignExtend imm_0 8 8) 7 8);
      (v_5 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 127 0) v_4) (expression.bv_nat 128 6)) 0 128);
      v_6 <- eval (shl (expression.bv_nat 128 18446744073709551615) v_5);
      (v_7 : expression (bv 128)) <- eval (extract v_6 0 128);
      v_8 <- getRegister (lhs.of_reg r64_1);
      (v_9 : expression (bv 128)) <- eval (extract (bv_and (shl (concat (expression.bv_nat 64 0) v_8) v_5) v_6) 0 128);
      setRegister (lhs.of_reg xmm_2) (bv_or (bv_and v_3 (bv_xor v_7 (expression.bv_nat 128 340282366920938463463374607431768211455))) v_9);
      pure ()
    pat_end
