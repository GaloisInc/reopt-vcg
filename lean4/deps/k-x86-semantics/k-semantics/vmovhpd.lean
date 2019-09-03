def vmovhpd1 : instruction :=
  definst "vmovhpd" $ do
    pattern fun (v_2828 : Mem) (v_2829 : reg (bv 128)) (v_2830 : reg (bv 128)) => do
      v_11113 <- evaluateAddress v_2828;
      v_11114 <- load v_11113 8;
      v_11115 <- getRegister v_2829;
      setRegister (lhs.of_reg v_2830) (concat v_11114 (extract v_11115 64 128));
      pure ()
    pat_end;
    pattern fun (v_2825 : reg (bv 128)) (v_2824 : Mem) => do
      v_13617 <- evaluateAddress v_2824;
      v_13618 <- getRegister v_2825;
      store v_13617 (extract v_13618 0 64) 8;
      pure ()
    pat_end
