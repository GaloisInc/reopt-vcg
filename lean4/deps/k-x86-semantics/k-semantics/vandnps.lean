def vandnps1 : instruction :=
  definst "vandnps" $ do
    pattern fun (v_2766 : reg (bv 128)) (v_2767 : reg (bv 128)) (v_2768 : reg (bv 128)) => do
      v_5145 <- getRegister v_2767;
      v_5147 <- getRegister v_2766;
      setRegister (lhs.of_reg v_2768) (bv_and (bv_xor v_5145 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_5147);
      pure ()
    pat_end;
    pattern fun (v_2776 : reg (bv 256)) (v_2777 : reg (bv 256)) (v_2778 : reg (bv 256)) => do
      v_5155 <- getRegister v_2777;
      v_5157 <- getRegister v_2776;
      setRegister (lhs.of_reg v_2778) (bv_and (bv_xor v_5155 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_5157);
      pure ()
    pat_end;
    pattern fun (v_2760 : Mem) (v_2761 : reg (bv 128)) (v_2762 : reg (bv 128)) => do
      v_9404 <- getRegister v_2761;
      v_9406 <- evaluateAddress v_2760;
      v_9407 <- load v_9406 16;
      setRegister (lhs.of_reg v_2762) (bv_and (bv_xor v_9404 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_9407);
      pure ()
    pat_end;
    pattern fun (v_2771 : Mem) (v_2772 : reg (bv 256)) (v_2773 : reg (bv 256)) => do
      v_9410 <- getRegister v_2772;
      v_9412 <- evaluateAddress v_2771;
      v_9413 <- load v_9412 32;
      setRegister (lhs.of_reg v_2773) (bv_and (bv_xor v_9410 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_9413);
      pure ()
    pat_end
