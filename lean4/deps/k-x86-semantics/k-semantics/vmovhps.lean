def vmovhps1 : instruction :=
  definst "vmovhps" $ do
    pattern fun (v_2913 : Mem) (v_2914 : reg (bv 128)) (v_2915 : reg (bv 128)) => do
      v_10208 <- evaluateAddress v_2913;
      v_10209 <- load v_10208 8;
      v_10210 <- getRegister v_2914;
      setRegister (lhs.of_reg v_2915) (concat v_10209 (extract v_10210 64 128));
      pure ()
    pat_end;
    pattern fun (v_2910 : reg (bv 128)) (v_2909 : Mem) => do
      v_12451 <- evaluateAddress v_2909;
      v_12452 <- getRegister v_2910;
      store v_12451 (extract v_12452 0 64) 8;
      pure ()
    pat_end
