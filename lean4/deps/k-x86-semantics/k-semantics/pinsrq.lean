def pinsrq1 : instruction :=
  definst "pinsrq" $ do
    pattern fun (v_2574 : imm int) (v_2572 : reg (bv 64)) (v_2573 : reg (bv 128)) => do
      v_4477 <- getRegister v_2573;
      v_4482 <- eval (extract (shl (concat (expression.bv_nat 127 0) (extract (handleImmediateWithSignExtend v_2574 8 8) 7 8)) (expression.bv_nat 128 6)) 0 128);
      v_4483 <- eval (shl (expression.bv_nat 128 18446744073709551615) v_4482);
      v_4487 <- getRegister v_2572;
      setRegister (lhs.of_reg v_2573) (bv_or (bv_and v_4477 (bv_xor (extract v_4483 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 64 0) v_4487) v_4482) v_4483) 0 128));
      pure ()
    pat_end
