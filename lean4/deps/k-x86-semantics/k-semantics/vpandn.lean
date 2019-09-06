def vpandn1 : instruction :=
  definst "vpandn" $ do
    pattern fun (v_2634 : reg (bv 128)) (v_2635 : reg (bv 128)) (v_2636 : reg (bv 128)) => do
      v_5754 <- getRegister v_2635;
      v_5756 <- getRegister v_2634;
      setRegister (lhs.of_reg v_2636) (bv_and (bv_xor v_5754 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_5756);
      pure ()
    pat_end;
    pattern fun (v_2645 : reg (bv 256)) (v_2646 : reg (bv 256)) (v_2647 : reg (bv 256)) => do
      v_5764 <- getRegister v_2646;
      v_5766 <- getRegister v_2645;
      setRegister (lhs.of_reg v_2647) (bv_and (bv_xor v_5764 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_5766);
      pure ()
    pat_end;
    pattern fun (v_2629 : Mem) (v_2630 : reg (bv 128)) (v_2631 : reg (bv 128)) => do
      v_14456 <- getRegister v_2630;
      v_14458 <- evaluateAddress v_2629;
      v_14459 <- load v_14458 16;
      setRegister (lhs.of_reg v_2631) (bv_and (bv_xor v_14456 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_14459);
      pure ()
    pat_end;
    pattern fun (v_2640 : Mem) (v_2641 : reg (bv 256)) (v_2642 : reg (bv 256)) => do
      v_14462 <- getRegister v_2641;
      v_14464 <- evaluateAddress v_2640;
      v_14465 <- load v_14464 32;
      setRegister (lhs.of_reg v_2642) (bv_and (bv_xor v_14462 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_14465);
      pure ()
    pat_end
