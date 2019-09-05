def vpinsrd1 : instruction :=
  definst "vpinsrd" $ do
    pattern fun (v_3368 : imm int) (v_3372 : reg (bv 32)) (v_3370 : reg (bv 128)) (v_3371 : reg (bv 128)) => do
      v_9623 <- getRegister v_3370;
      v_9628 <- eval (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_3368 8 8) 6 8)) (expression.bv_nat 128 5)) 0 128);
      v_9629 <- eval (shl (expression.bv_nat 128 4294967295) v_9628);
      v_9633 <- getRegister v_3372;
      setRegister (lhs.of_reg v_3371) (bv_or (bv_and v_9623 (bv_xor (extract v_9629 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 96 0) v_9633) v_9628) v_9629) 0 128));
      pure ()
    pat_end;
    pattern fun (v_3362 : imm int) (v_3363 : Mem) (v_3364 : reg (bv 128)) (v_3365 : reg (bv 128)) => do
      v_17986 <- getRegister v_3364;
      v_17991 <- eval (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_3362 8 8) 6 8)) (expression.bv_nat 128 5)) 0 128);
      v_17992 <- eval (shl (expression.bv_nat 128 4294967295) v_17991);
      v_17996 <- evaluateAddress v_3363;
      v_17997 <- load v_17996 4;
      setRegister (lhs.of_reg v_3365) (bv_or (bv_and v_17986 (bv_xor (extract v_17992 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 96 0) v_17997) v_17991) v_17992) 0 128));
      pure ()
    pat_end
