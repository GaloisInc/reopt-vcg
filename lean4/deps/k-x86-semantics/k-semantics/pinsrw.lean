def pinsrw1 : instruction :=
  definst "pinsrw" $ do
    pattern fun (v_2611 : imm int) (v_2613 : reg (bv 32)) (v_2612 : reg (bv 128)) => do
      v_4526 <- getRegister v_2612;
      v_4531 <- eval (extract (shl (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_2611 8 8) 5 8)) (expression.bv_nat 128 4)) 0 128);
      v_4532 <- eval (shl (expression.bv_nat 128 65535) v_4531);
      v_4536 <- getRegister v_2613;
      setRegister (lhs.of_reg v_2612) (bv_or (bv_and v_4526 (bv_xor (extract v_4532 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 96 0) v_4536) v_4531) v_4532) 0 128));
      pure ()
    pat_end;
    pattern fun (v_2607 : imm int) (v_2606 : Mem) (v_2608 : reg (bv 128)) => do
      v_11388 <- getRegister v_2608;
      v_11393 <- eval (extract (shl (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_2607 8 8) 5 8)) (expression.bv_nat 128 4)) 0 128);
      v_11394 <- eval (shl (expression.bv_nat 128 65535) v_11393);
      v_11398 <- evaluateAddress v_2606;
      v_11399 <- load v_11398 2;
      setRegister (lhs.of_reg v_2608) (bv_or (bv_and v_11388 (bv_xor (extract v_11394 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 112 0) v_11399) v_11393) v_11394) 0 128));
      pure ()
    pat_end
