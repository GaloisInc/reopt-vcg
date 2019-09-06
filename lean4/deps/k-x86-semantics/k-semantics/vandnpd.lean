def vandnpd1 : instruction :=
  definst "vandnpd" $ do
    pattern fun (v_2771 : reg (bv 128)) (v_2772 : reg (bv 128)) (v_2773 : reg (bv 128)) => do
      v_5152 <- getRegister v_2772;
      v_5154 <- getRegister v_2771;
      setRegister (lhs.of_reg v_2773) (bv_and (bv_xor v_5152 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_5154);
      pure ()
    pat_end;
    pattern fun (v_2779 : reg (bv 256)) (v_2780 : reg (bv 256)) (v_2781 : reg (bv 256)) => do
      v_5162 <- getRegister v_2780;
      v_5164 <- getRegister v_2779;
      setRegister (lhs.of_reg v_2781) (bv_and (bv_xor v_5162 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_5164);
      pure ()
    pat_end;
    pattern fun (v_2763 : Mem) (v_2766 : reg (bv 128)) (v_2767 : reg (bv 128)) => do
      v_9419 <- getRegister v_2766;
      v_9421 <- evaluateAddress v_2763;
      v_9422 <- load v_9421 16;
      setRegister (lhs.of_reg v_2767) (bv_and (bv_xor v_9419 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_9422);
      pure ()
    pat_end;
    pattern fun (v_2774 : Mem) (v_2775 : reg (bv 256)) (v_2776 : reg (bv 256)) => do
      v_9425 <- getRegister v_2775;
      v_9427 <- evaluateAddress v_2774;
      v_9428 <- load v_9427 32;
      setRegister (lhs.of_reg v_2776) (bv_and (bv_xor v_9425 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_9428);
      pure ()
    pat_end
