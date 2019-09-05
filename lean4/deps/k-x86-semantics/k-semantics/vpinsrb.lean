def vpinsrb1 : instruction :=
  definst "vpinsrb" $ do
    pattern fun (v_3355 : imm int) (v_3359 : reg (bv 32)) (v_3357 : reg (bv 128)) (v_3358 : reg (bv 128)) => do
      v_9600 <- getRegister v_3357;
      v_9605 <- eval (extract (shl (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_3355 8 8) 4 8)) (expression.bv_nat 128 3)) 0 128);
      v_9606 <- eval (shl (expression.bv_nat 128 255) v_9605);
      v_9610 <- getRegister v_3359;
      setRegister (lhs.of_reg v_3358) (bv_or (bv_and v_9600 (bv_xor (extract v_9606 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 96 0) v_9610) v_9605) v_9606) 0 128));
      pure ()
    pat_end;
    pattern fun (v_3349 : imm int) (v_3350 : Mem) (v_3351 : reg (bv 128)) (v_3352 : reg (bv 128)) => do
      v_17968 <- getRegister v_3351;
      v_17973 <- eval (extract (shl (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_3349 8 8) 4 8)) (expression.bv_nat 128 3)) 0 128);
      v_17974 <- eval (shl (expression.bv_nat 128 255) v_17973);
      v_17978 <- evaluateAddress v_3350;
      v_17979 <- load v_17978 1;
      setRegister (lhs.of_reg v_3352) (bv_or (bv_and v_17968 (bv_xor (extract v_17974 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 120 0) v_17979) v_17973) v_17974) 0 128));
      pure ()
    pat_end
