def vandnps1 : instruction :=
  definst "vandnps" $ do
    pattern fun (v_2715 : reg (bv 128)) (v_2716 : reg (bv 128)) (v_2717 : reg (bv 128)) => do
      v_5640 <- getRegister v_2716;
      v_5642 <- getRegister v_2715;
      setRegister (lhs.of_reg v_2717) (bv_and (bv_xor v_5640 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_5642);
      pure ()
    pat_end;
    pattern fun (v_2723 : reg (bv 256)) (v_2724 : reg (bv 256)) (v_2725 : reg (bv 256)) => do
      v_5650 <- getRegister v_2724;
      v_5652 <- getRegister v_2723;
      setRegister (lhs.of_reg v_2725) (bv_and (bv_xor v_5650 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_5652);
      pure ()
    pat_end;
    pattern fun (v_2707 : Mem) (v_2710 : reg (bv 128)) (v_2711 : reg (bv 128)) => do
      v_11142 <- getRegister v_2710;
      v_11144 <- evaluateAddress v_2707;
      v_11145 <- load v_11144 16;
      setRegister (lhs.of_reg v_2711) (bv_and (bv_xor v_11142 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_11145);
      pure ()
    pat_end;
    pattern fun (v_2718 : Mem) (v_2719 : reg (bv 256)) (v_2720 : reg (bv 256)) => do
      v_11148 <- getRegister v_2719;
      v_11150 <- evaluateAddress v_2718;
      v_11151 <- load v_11150 32;
      setRegister (lhs.of_reg v_2720) (bv_and (bv_xor v_11148 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_11151);
      pure ()
    pat_end
