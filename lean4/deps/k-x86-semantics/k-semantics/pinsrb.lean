def pinsrb1 : instruction :=
  definst "pinsrb" $ do
    pattern fun (v_2583 : imm int) (v_2585 : reg (bv 32)) (v_2584 : reg (bv 128)) => do
      v_4465 <- getRegister v_2584;
      v_4470 <- eval (extract (shl (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_2583 8 8) 4 8)) (expression.bv_nat 128 3)) 0 128);
      v_4471 <- eval (shl (expression.bv_nat 128 255) v_4470);
      v_4475 <- getRegister v_2585;
      setRegister (lhs.of_reg v_2584) (bv_or (bv_and v_4465 (bv_xor (extract v_4471 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 96 0) v_4475) v_4470) v_4471) 0 128));
      pure ()
    pat_end;
    pattern fun (v_2579 : imm int) (v_2578 : Mem) (v_2580 : reg (bv 128)) => do
      v_11352 <- getRegister v_2580;
      v_11357 <- eval (extract (shl (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_2579 8 8) 4 8)) (expression.bv_nat 128 3)) 0 128);
      v_11358 <- eval (shl (expression.bv_nat 128 255) v_11357);
      v_11362 <- evaluateAddress v_2578;
      v_11363 <- load v_11362 1;
      setRegister (lhs.of_reg v_2580) (bv_or (bv_and v_11352 (bv_xor (extract v_11358 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 120 0) v_11363) v_11357) v_11358) 0 128));
      pure ()
    pat_end
