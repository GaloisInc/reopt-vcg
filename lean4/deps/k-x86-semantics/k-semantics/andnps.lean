def andnps1 : instruction :=
  definst "andnps" $ do
    pattern fun (v_2816 : reg (bv 128)) (v_2817 : reg (bv 128)) => do
      v_5586 <- getRegister v_2817;
      v_5588 <- getRegister v_2816;
      setRegister (lhs.of_reg v_2817) (bv_and (bv_xor v_5586 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_5588);
      pure ()
    pat_end;
    pattern fun (v_2811 : Mem) (v_2812 : reg (bv 128)) => do
      v_9670 <- getRegister v_2812;
      v_9672 <- evaluateAddress v_2811;
      v_9673 <- load v_9672 16;
      setRegister (lhs.of_reg v_2812) (bv_and (bv_xor v_9670 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_9673);
      pure ()
    pat_end
