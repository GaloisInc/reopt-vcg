def vpinsrq1 : instruction :=
  definst "vpinsrq" $ do
    pattern fun (v_3408 : imm int) (v_3412 : reg (bv 64)) (v_3409 : reg (bv 128)) (v_3410 : reg (bv 128)) => do
      v_9673 <- getRegister v_3409;
      v_9678 <- eval (extract (shl (concat (expression.bv_nat 127 0) (extract (handleImmediateWithSignExtend v_3408 8 8) 7 8)) (expression.bv_nat 128 6)) 0 128);
      v_9679 <- eval (shl (expression.bv_nat 128 18446744073709551615) v_9678);
      v_9683 <- getRegister v_3412;
      setRegister (lhs.of_reg v_3410) (bv_or (bv_and v_9673 (bv_xor (extract v_9679 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 64 0) v_9683) v_9678) v_9679) 0 128));
      pure ()
    pat_end;
    pattern fun (v_3403 : imm int) (v_3402 : Mem) (v_3404 : reg (bv 128)) (v_3405 : reg (bv 128)) => do
      v_18031 <- getRegister v_3404;
      v_18036 <- eval (extract (shl (concat (expression.bv_nat 127 0) (extract (handleImmediateWithSignExtend v_3403 8 8) 7 8)) (expression.bv_nat 128 6)) 0 128);
      v_18037 <- eval (shl (expression.bv_nat 128 18446744073709551615) v_18036);
      v_18041 <- evaluateAddress v_3402;
      v_18042 <- load v_18041 8;
      setRegister (lhs.of_reg v_3405) (bv_or (bv_and v_18031 (bv_xor (extract v_18037 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 64 0) v_18042) v_18036) v_18037) 0 128));
      pure ()
    pat_end
