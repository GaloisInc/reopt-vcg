def vandpd1 : instruction :=
  definst "vandpd" $ do
    pattern fun (v_2729 : Mem) (v_2732 : reg (bv 128)) (v_2733 : reg (bv 128)) => do
      v_11154 <- getRegister v_2732;
      v_11155 <- evaluateAddress v_2729;
      v_11156 <- load v_11155 16;
      setRegister (lhs.of_reg v_2733) (bv_and v_11154 v_11156);
      pure ()
    pat_end;
    pattern fun (v_2740 : Mem) (v_2741 : reg (bv 256)) (v_2742 : reg (bv 256)) => do
      v_11159 <- getRegister v_2741;
      v_11160 <- evaluateAddress v_2740;
      v_11161 <- load v_11160 32;
      setRegister (lhs.of_reg v_2742) (bv_and v_11159 v_11161);
      pure ()
    pat_end
