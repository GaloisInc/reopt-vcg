def vandnpd1 : instruction :=
  definst "vandnpd" $ do
    pattern fun (v_2672 : Mem) (v_2675 : reg (bv 128)) (v_2676 : reg (bv 128)) => do
      v_9580 <- getRegister v_2675;
      v_9584 <- evaluateAddress v_2672;
      v_9585 <- load v_9584 16;
      setRegister (lhs.of_reg v_2676) (bv_and (bv_xor v_9580 (mi (bitwidthMInt v_9580) -1)) v_9585);
      pure ()
    pat_end;
    pattern fun (v_2683 : Mem) (v_2684 : reg (bv 256)) (v_2685 : reg (bv 256)) => do
      v_9588 <- getRegister v_2684;
      v_9592 <- evaluateAddress v_2683;
      v_9593 <- load v_9592 32;
      setRegister (lhs.of_reg v_2685) (bv_and (bv_xor v_9588 (mi (bitwidthMInt v_9588) -1)) v_9593);
      pure ()
    pat_end
