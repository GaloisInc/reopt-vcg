def vandpd1 : instruction :=
  definst "vandpd" $ do
    pattern fun (v_2716 : Mem) (v_2719 : reg (bv 128)) (v_2720 : reg (bv 128)) => do
      v_9612 <- getRegister v_2719;
      v_9613 <- evaluateAddress v_2716;
      v_9614 <- load v_9613 16;
      setRegister (lhs.of_reg v_2720) (bv_and v_9612 v_9614);
      pure ()
    pat_end;
    pattern fun (v_2727 : Mem) (v_2728 : reg (bv 256)) (v_2729 : reg (bv 256)) => do
      v_9617 <- getRegister v_2728;
      v_9618 <- evaluateAddress v_2727;
      v_9619 <- load v_9618 32;
      setRegister (lhs.of_reg v_2729) (bv_and v_9617 v_9619);
      pure ()
    pat_end
