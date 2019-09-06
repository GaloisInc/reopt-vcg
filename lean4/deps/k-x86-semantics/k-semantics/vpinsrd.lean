def vpinsrd1 : instruction :=
  definst "vpinsrd" $ do
    pattern fun (v_3395 : imm int) (v_3398 : reg (bv 32)) (v_3396 : reg (bv 128)) (v_3397 : reg (bv 128)) => do
      v_9650 <- getRegister v_3396;
      v_9655 <- eval (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_3395 8 8) 6 8)) (expression.bv_nat 128 5)) 0 128);
      v_9656 <- eval (shl (expression.bv_nat 128 4294967295) v_9655);
      v_9660 <- getRegister v_3398;
      setRegister (lhs.of_reg v_3397) (bv_or (bv_and v_9650 (bv_xor (extract v_9656 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 96 0) v_9660) v_9655) v_9656) 0 128));
      pure ()
    pat_end;
    pattern fun (v_3390 : imm int) (v_3389 : Mem) (v_3391 : reg (bv 128)) (v_3392 : reg (bv 128)) => do
      v_18013 <- getRegister v_3391;
      v_18018 <- eval (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_3390 8 8) 6 8)) (expression.bv_nat 128 5)) 0 128);
      v_18019 <- eval (shl (expression.bv_nat 128 4294967295) v_18018);
      v_18023 <- evaluateAddress v_3389;
      v_18024 <- load v_18023 4;
      setRegister (lhs.of_reg v_3392) (bv_or (bv_and v_18013 (bv_xor (extract v_18019 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 96 0) v_18024) v_18018) v_18019) 0 128));
      pure ()
    pat_end
