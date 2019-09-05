def vandnpd1 : instruction :=
  definst "vandnpd" $ do
    pattern fun (v_2744 : reg (bv 128)) (v_2745 : reg (bv 128)) (v_2746 : reg (bv 128)) => do
      v_5125 <- getRegister v_2745;
      v_5127 <- getRegister v_2744;
      setRegister (lhs.of_reg v_2746) (bv_and (bv_xor v_5125 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_5127);
      pure ()
    pat_end;
    pattern fun (v_2754 : reg (bv 256)) (v_2755 : reg (bv 256)) (v_2756 : reg (bv 256)) => do
      v_5135 <- getRegister v_2755;
      v_5137 <- getRegister v_2754;
      setRegister (lhs.of_reg v_2756) (bv_and (bv_xor v_5135 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_5137);
      pure ()
    pat_end;
    pattern fun (v_2738 : Mem) (v_2739 : reg (bv 128)) (v_2740 : reg (bv 128)) => do
      v_9392 <- getRegister v_2739;
      v_9394 <- evaluateAddress v_2738;
      v_9395 <- load v_9394 16;
      setRegister (lhs.of_reg v_2740) (bv_and (bv_xor v_9392 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_9395);
      pure ()
    pat_end;
    pattern fun (v_2749 : Mem) (v_2750 : reg (bv 256)) (v_2751 : reg (bv 256)) => do
      v_9398 <- getRegister v_2750;
      v_9400 <- evaluateAddress v_2749;
      v_9401 <- load v_9400 32;
      setRegister (lhs.of_reg v_2751) (bv_and (bv_xor v_9398 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_9401);
      pure ()
    pat_end
