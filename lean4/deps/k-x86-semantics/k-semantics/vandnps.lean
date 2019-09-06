def vandnps1 : instruction :=
  definst "vandnps" $ do
    pattern fun (v_2793 : reg (bv 128)) (v_2794 : reg (bv 128)) (v_2795 : reg (bv 128)) => do
      v_5172 <- getRegister v_2794;
      v_5174 <- getRegister v_2793;
      setRegister (lhs.of_reg v_2795) (bv_and (bv_xor v_5172 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_5174);
      pure ()
    pat_end;
    pattern fun (v_2801 : reg (bv 256)) (v_2802 : reg (bv 256)) (v_2803 : reg (bv 256)) => do
      v_5182 <- getRegister v_2802;
      v_5184 <- getRegister v_2801;
      setRegister (lhs.of_reg v_2803) (bv_and (bv_xor v_5182 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_5184);
      pure ()
    pat_end;
    pattern fun (v_2785 : Mem) (v_2788 : reg (bv 128)) (v_2789 : reg (bv 128)) => do
      v_9431 <- getRegister v_2788;
      v_9433 <- evaluateAddress v_2785;
      v_9434 <- load v_9433 16;
      setRegister (lhs.of_reg v_2789) (bv_and (bv_xor v_9431 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_9434);
      pure ()
    pat_end;
    pattern fun (v_2796 : Mem) (v_2797 : reg (bv 256)) (v_2798 : reg (bv 256)) => do
      v_9437 <- getRegister v_2797;
      v_9439 <- evaluateAddress v_2796;
      v_9440 <- load v_9439 32;
      setRegister (lhs.of_reg v_2798) (bv_and (bv_xor v_9437 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_9440);
      pure ()
    pat_end
