def andnpd1 : instruction :=
  definst "andnpd" $ do
    pattern fun (v_2807 : reg (bv 128)) (v_2808 : reg (bv 128)) => do
      v_5577 <- getRegister v_2808;
      v_5579 <- getRegister v_2807;
      setRegister (lhs.of_reg v_2808) (bv_and (bv_xor v_5577 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_5579);
      pure ()
    pat_end;
    pattern fun (v_2802 : Mem) (v_2803 : reg (bv 128)) => do
      v_9664 <- getRegister v_2803;
      v_9666 <- evaluateAddress v_2802;
      v_9667 <- load v_9666 16;
      setRegister (lhs.of_reg v_2803) (bv_and (bv_xor v_9664 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_9667);
      pure ()
    pat_end
