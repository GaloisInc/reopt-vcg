def pinsrq : instruction :=
  definst "pinsrq" $ do
    pattern fun (imm_0 : imm int) (r64_1 : reg (bv 64)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      v_4 <- eval (extract (shl (concat (expression.bv_nat 127 0) (extract (handleImmediateWithSignExtend imm_0 8 8) 7 8)) (expression.bv_nat 128 6)) 0 128);
      v_5 <- eval (shl (expression.bv_nat 128 18446744073709551615) v_4);
      v_6 <- getRegister (lhs.of_reg r64_1);
      setRegister (lhs.of_reg xmm_2) (bv_or (bv_and v_3 (bv_xor (extract v_5 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 64 0) v_6) v_4) v_5) 0 128));
      pure ()
    pat_end
