def vpinsrw1 : instruction :=
  definst "vpinsrw" $ do
    pattern fun (v_3394 : imm int) (v_3398 : reg (bv 32)) (v_3396 : reg (bv 128)) (v_3397 : reg (bv 128)) => do
      v_9669 <- getRegister v_3396;
      v_9674 <- eval (extract (shl (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_3394 8 8) 5 8)) (expression.bv_nat 128 4)) 0 128);
      v_9675 <- eval (shl (expression.bv_nat 128 65535) v_9674);
      v_9679 <- getRegister v_3398;
      setRegister (lhs.of_reg v_3397) (bv_or (bv_and v_9669 (bv_xor (extract v_9675 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 96 0) v_9679) v_9674) v_9675) 0 128));
      pure ()
    pat_end;
    pattern fun (v_3388 : imm int) (v_3389 : Mem) (v_3390 : reg (bv 128)) (v_3391 : reg (bv 128)) => do
      v_18022 <- getRegister v_3390;
      v_18027 <- eval (extract (shl (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_3388 8 8) 5 8)) (expression.bv_nat 128 4)) 0 128);
      v_18028 <- eval (shl (expression.bv_nat 128 65535) v_18027);
      v_18032 <- evaluateAddress v_3389;
      v_18033 <- load v_18032 2;
      setRegister (lhs.of_reg v_3391) (bv_or (bv_and v_18022 (bv_xor (extract v_18028 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 112 0) v_18033) v_18027) v_18028) 0 128));
      pure ()
    pat_end
