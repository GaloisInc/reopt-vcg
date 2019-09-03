def vpinsrd1 : instruction :=
  definst "vpinsrd" $ do
    pattern fun (v_3319 : imm int) (v_3321 : reg (bv 32)) (v_3315 : reg (bv 128)) (v_3316 : reg (bv 128)) => do
      v_9769 <- getRegister v_3315;
      v_9775 <- eval (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_3319 8 8) 6 8)) 5) 0 128));
      v_9777 <- eval (extract (shl (expression.bv_nat 128 4294967295) v_9775) 0 128);
      v_9780 <- getRegister v_3321;
      setRegister (lhs.of_reg v_3316) (bv_or (bv_and v_9769 (bv_xor v_9777 (expression.bv_nat 128 340282366920938463463374607431768211455))) (bv_and (extract (shl (concat (expression.bv_nat 96 0) v_9780) v_9775) 0 128) v_9777));
      pure ()
    pat_end;
    pattern fun (v_3314 : imm int) (v_3313 : Mem) (v_3309 : reg (bv 128)) (v_3310 : reg (bv 128)) => do
      v_18374 <- getRegister v_3309;
      v_18380 <- eval (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_3314 8 8) 6 8)) 5) 0 128));
      v_18382 <- eval (extract (shl (expression.bv_nat 128 4294967295) v_18380) 0 128);
      v_18385 <- evaluateAddress v_3313;
      v_18386 <- load v_18385 4;
      setRegister (lhs.of_reg v_3310) (bv_or (bv_and v_18374 (bv_xor v_18382 (expression.bv_nat 128 340282366920938463463374607431768211455))) (bv_and (extract (shl (concat (expression.bv_nat 96 0) v_18386) v_18380) 0 128) v_18382));
      pure ()
    pat_end
