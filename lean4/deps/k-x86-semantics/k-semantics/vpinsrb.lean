def vpinsrb1 : instruction :=
  definst "vpinsrb" $ do
    pattern fun (v_3306 : imm int) (v_3308 : reg (bv 32)) (v_3302 : reg (bv 128)) (v_3303 : reg (bv 128)) => do
      v_9745 <- getRegister v_3302;
      v_9751 <- eval (uvalueMInt (extract (shl (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_3306 8 8) 4 8)) 3) 0 128));
      v_9753 <- eval (extract (shl (expression.bv_nat 128 255) v_9751) 0 128);
      v_9756 <- getRegister v_3308;
      setRegister (lhs.of_reg v_3303) (bv_or (bv_and v_9745 (bv_xor v_9753 (expression.bv_nat 128 340282366920938463463374607431768211455))) (bv_and (extract (shl (concat (expression.bv_nat 96 0) v_9756) v_9751) 0 128) v_9753));
      pure ()
    pat_end;
    pattern fun (v_3301 : imm int) (v_3300 : Mem) (v_3296 : reg (bv 128)) (v_3297 : reg (bv 128)) => do
      v_18355 <- getRegister v_3296;
      v_18361 <- eval (uvalueMInt (extract (shl (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_3301 8 8) 4 8)) 3) 0 128));
      v_18363 <- eval (extract (shl (expression.bv_nat 128 255) v_18361) 0 128);
      v_18366 <- evaluateAddress v_3300;
      v_18367 <- load v_18366 1;
      setRegister (lhs.of_reg v_3297) (bv_or (bv_and v_18355 (bv_xor v_18363 (expression.bv_nat 128 340282366920938463463374607431768211455))) (bv_and (extract (shl (concat (expression.bv_nat 120 0) v_18367) v_18361) 0 128) v_18363));
      pure ()
    pat_end
