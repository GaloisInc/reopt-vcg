def pinsrb1 : instruction :=
  definst "pinsrb" $ do
    pattern fun (v_2557 : imm int) (v_2556 : reg (bv 32)) (v_2555 : reg (bv 128)) => do
      v_4438 <- getRegister v_2555;
      v_4443 <- eval (extract (shl (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_2557 8 8) 4 8)) (expression.bv_nat 128 3)) 0 128);
      v_4444 <- eval (shl (expression.bv_nat 128 255) v_4443);
      v_4448 <- getRegister v_2556;
      setRegister (lhs.of_reg v_2555) (bv_or (bv_and v_4438 (bv_xor (extract v_4444 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 96 0) v_4448) v_4443) v_4444) 0 128));
      pure ()
    pat_end;
    pattern fun (v_2551 : imm int) (v_2552 : Mem) (v_2550 : reg (bv 128)) => do
      v_11376 <- getRegister v_2550;
      v_11381 <- eval (extract (shl (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_2551 8 8) 4 8)) (expression.bv_nat 128 3)) 0 128);
      v_11382 <- eval (shl (expression.bv_nat 128 255) v_11381);
      v_11386 <- evaluateAddress v_2552;
      v_11387 <- load v_11386 1;
      setRegister (lhs.of_reg v_2550) (bv_or (bv_and v_11376 (bv_xor (extract v_11382 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 120 0) v_11387) v_11381) v_11382) 0 128));
      pure ()
    pat_end
