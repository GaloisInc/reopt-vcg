def vpinsrb1 : instruction :=
  definst "vpinsrb" $ do
    pattern fun (v_3382 : imm int) (v_3385 : reg (bv 32)) (v_3383 : reg (bv 128)) (v_3384 : reg (bv 128)) => do
      v_9627 <- getRegister v_3383;
      v_9632 <- eval (extract (shl (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_3382 8 8) 4 8)) (expression.bv_nat 128 3)) 0 128);
      v_9633 <- eval (shl (expression.bv_nat 128 255) v_9632);
      v_9637 <- getRegister v_3385;
      setRegister (lhs.of_reg v_3384) (bv_or (bv_and v_9627 (bv_xor (extract v_9633 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 96 0) v_9637) v_9632) v_9633) 0 128));
      pure ()
    pat_end;
    pattern fun (v_3377 : imm int) (v_3376 : Mem) (v_3378 : reg (bv 128)) (v_3379 : reg (bv 128)) => do
      v_17995 <- getRegister v_3378;
      v_18000 <- eval (extract (shl (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_3377 8 8) 4 8)) (expression.bv_nat 128 3)) 0 128);
      v_18001 <- eval (shl (expression.bv_nat 128 255) v_18000);
      v_18005 <- evaluateAddress v_3376;
      v_18006 <- load v_18005 1;
      setRegister (lhs.of_reg v_3379) (bv_or (bv_and v_17995 (bv_xor (extract v_18001 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 120 0) v_18006) v_18000) v_18001) 0 128));
      pure ()
    pat_end
