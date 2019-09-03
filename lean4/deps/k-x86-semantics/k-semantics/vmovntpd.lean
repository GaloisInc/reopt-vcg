def vmovntpd1 : instruction :=
  definst "vmovntpd" $ do
    pattern fun (v_2910 : reg (bv 128)) (v_2909 : Mem) => do
      v_12759 <- evaluateAddress v_2909;
      v_12760 <- getRegister v_2910;
      store v_12759 v_12760 16;
      pure ()
    pat_end;
    pattern fun (v_2914 : reg (bv 256)) (v_2913 : Mem) => do
      v_12762 <- evaluateAddress v_2913;
      v_12763 <- getRegister v_2914;
      store v_12762 v_12763 32;
      pure ()
    pat_end
