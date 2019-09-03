def vpandn1 : instruction :=
  definst "vpandn" $ do
    pattern fun (v_2554 : reg (bv 128)) (v_2555 : reg (bv 128)) (v_2556 : reg (bv 128)) => do
      v_5750 <- getRegister v_2555;
      v_5752 <- getRegister v_2554;
      setRegister (lhs.of_reg v_2556) (bv_and (bv_xor v_5750 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_5752);
      pure ()
    pat_end;
    pattern fun (v_2568 : reg (bv 256)) (v_2569 : reg (bv 256)) (v_2570 : reg (bv 256)) => do
      v_5760 <- getRegister v_2569;
      v_5762 <- getRegister v_2568;
      setRegister (lhs.of_reg v_2570) (bv_and (bv_xor v_5760 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_5762);
      pure ()
    pat_end;
    pattern fun (v_2553 : Mem) (v_2549 : reg (bv 128)) (v_2550 : reg (bv 128)) => do
      v_14700 <- getRegister v_2549;
      v_14702 <- evaluateAddress v_2553;
      v_14703 <- load v_14702 16;
      setRegister (lhs.of_reg v_2550) (bv_and (bv_xor v_14700 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_14703);
      pure ()
    pat_end;
    pattern fun (v_2562 : Mem) (v_2563 : reg (bv 256)) (v_2564 : reg (bv 256)) => do
      v_14706 <- getRegister v_2563;
      v_14708 <- evaluateAddress v_2562;
      v_14709 <- load v_14708 32;
      setRegister (lhs.of_reg v_2564) (bv_and (bv_xor v_14706 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_14709);
      pure ()
    pat_end
