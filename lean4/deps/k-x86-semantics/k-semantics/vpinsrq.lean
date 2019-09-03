def vpinsrq1 : instruction :=
  definst "vpinsrq" $ do
    pattern fun (v_3332 : imm int) (v_3333 : reg (bv 64)) (v_3328 : reg (bv 128)) (v_3329 : reg (bv 128)) => do
      v_9793 <- getRegister v_3328;
      v_9799 <- eval (uvalueMInt (extract (shl (concat (expression.bv_nat 127 0) (extract (handleImmediateWithSignExtend v_3332 8 8) 7 8)) 6) 0 128));
      v_9801 <- eval (extract (shl (expression.bv_nat 128 18446744073709551615) v_9799) 0 128);
      v_9804 <- getRegister v_3333;
      setRegister (lhs.of_reg v_3329) (bv_or (bv_and v_9793 (bv_xor v_9801 (expression.bv_nat 128 340282366920938463463374607431768211455))) (bv_and (extract (shl (concat (expression.bv_nat 64 0) v_9804) v_9799) 0 128) v_9801));
      pure ()
    pat_end;
    pattern fun (v_3327 : imm int) (v_3326 : Mem) (v_3322 : reg (bv 128)) (v_3323 : reg (bv 128)) => do
      v_18393 <- getRegister v_3322;
      v_18399 <- eval (uvalueMInt (extract (shl (concat (expression.bv_nat 127 0) (extract (handleImmediateWithSignExtend v_3327 8 8) 7 8)) 6) 0 128));
      v_18401 <- eval (extract (shl (expression.bv_nat 128 18446744073709551615) v_18399) 0 128);
      v_18404 <- evaluateAddress v_3326;
      v_18405 <- load v_18404 8;
      setRegister (lhs.of_reg v_3323) (bv_or (bv_and v_18393 (bv_xor v_18401 (expression.bv_nat 128 340282366920938463463374607431768211455))) (bv_and (extract (shl (concat (expression.bv_nat 64 0) v_18405) v_18399) 0 128) v_18401));
      pure ()
    pat_end
