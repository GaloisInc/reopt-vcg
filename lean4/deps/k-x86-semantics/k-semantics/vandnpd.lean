def vandnpd1 : instruction :=
  definst "vandnpd" $ do
    pattern fun (v_2693 : reg (bv 128)) (v_2694 : reg (bv 128)) (v_2695 : reg (bv 128)) => do
      v_5620 <- getRegister v_2694;
      v_5622 <- getRegister v_2693;
      setRegister (lhs.of_reg v_2695) (bv_and (bv_xor v_5620 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_5622);
      pure ()
    pat_end;
    pattern fun (v_2701 : reg (bv 256)) (v_2702 : reg (bv 256)) (v_2703 : reg (bv 256)) => do
      v_5630 <- getRegister v_2702;
      v_5632 <- getRegister v_2701;
      setRegister (lhs.of_reg v_2703) (bv_and (bv_xor v_5630 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_5632);
      pure ()
    pat_end;
    pattern fun (v_2685 : Mem) (v_2688 : reg (bv 128)) (v_2689 : reg (bv 128)) => do
      v_11130 <- getRegister v_2688;
      v_11132 <- evaluateAddress v_2685;
      v_11133 <- load v_11132 16;
      setRegister (lhs.of_reg v_2689) (bv_and (bv_xor v_11130 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_11133);
      pure ()
    pat_end;
    pattern fun (v_2696 : Mem) (v_2697 : reg (bv 256)) (v_2698 : reg (bv 256)) => do
      v_11136 <- getRegister v_2697;
      v_11138 <- evaluateAddress v_2696;
      v_11139 <- load v_11138 32;
      setRegister (lhs.of_reg v_2698) (bv_and (bv_xor v_11136 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_11139);
      pure ()
    pat_end
