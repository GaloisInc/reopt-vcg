def pinsrd1 : instruction :=
  definst "pinsrd" $ do
    pattern fun (v_2594 : imm int) (v_2596 : reg (bv 32)) (v_2595 : reg (bv 128)) => do
      v_4487 <- getRegister v_2595;
      v_4492 <- eval (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2594 8 8) 6 8)) (expression.bv_nat 128 5)) 0 128);
      v_4493 <- eval (shl (expression.bv_nat 128 4294967295) v_4492);
      v_4497 <- getRegister v_2596;
      setRegister (lhs.of_reg v_2595) (bv_or (bv_and v_4487 (bv_xor (extract v_4493 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 96 0) v_4497) v_4492) v_4493) 0 128));
      pure ()
    pat_end;
    pattern fun (v_2590 : imm int) (v_2589 : Mem) (v_2591 : reg (bv 128)) => do
      v_11370 <- getRegister v_2591;
      v_11375 <- eval (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2590 8 8) 6 8)) (expression.bv_nat 128 5)) 0 128);
      v_11376 <- eval (shl (expression.bv_nat 128 4294967295) v_11375);
      v_11380 <- evaluateAddress v_2589;
      v_11381 <- load v_11380 4;
      setRegister (lhs.of_reg v_2591) (bv_or (bv_and v_11370 (bv_xor (extract v_11376 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 96 0) v_11381) v_11375) v_11376) 0 128));
      pure ()
    pat_end
