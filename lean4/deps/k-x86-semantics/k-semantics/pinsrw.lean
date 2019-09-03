def pinsrw1 : instruction :=
  definst "pinsrw" $ do
    pattern fun (v_2534 : imm int) (v_2537 : reg (bv 32)) (v_2535 : reg (bv 128)) => do
      v_4451 <- getRegister v_2535;
      v_4457 <- eval (uvalueMInt (extract (shl (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_2534 8 8) 5 8)) 4) 0 128));
      v_4459 <- eval (extract (shl (expression.bv_nat 128 65535) v_4457) 0 128);
      v_4462 <- getRegister v_2537;
      setRegister (lhs.of_reg v_2535) (bv_or (bv_and v_4451 (bv_xor v_4459 (expression.bv_nat 128 340282366920938463463374607431768211455))) (bv_and (extract (shl (concat (expression.bv_nat 96 0) v_4462) v_4457) 0 128) v_4459));
      pure ()
    pat_end;
    pattern fun (v_2530 : imm int) (v_2529 : Mem) (v_2531 : reg (bv 128)) => do
      v_11537 <- getRegister v_2531;
      v_11543 <- eval (uvalueMInt (extract (shl (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_2530 8 8) 5 8)) 4) 0 128));
      v_11545 <- eval (extract (shl (expression.bv_nat 128 65535) v_11543) 0 128);
      v_11548 <- evaluateAddress v_2529;
      v_11549 <- load v_11548 2;
      setRegister (lhs.of_reg v_2531) (bv_or (bv_and v_11537 (bv_xor v_11545 (expression.bv_nat 128 340282366920938463463374607431768211455))) (bv_and (extract (shl (concat (expression.bv_nat 112 0) v_11549) v_11543) 0 128) v_11545));
      pure ()
    pat_end
