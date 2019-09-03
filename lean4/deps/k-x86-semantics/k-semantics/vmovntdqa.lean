def vmovntdqa1 : instruction :=
  definst "vmovntdqa" $ do
    pattern fun (v_2914 : Mem) (v_2915 : reg (bv 128)) => do
      v_11141 <- evaluateAddress v_2914;
      v_11142 <- load v_11141 16;
      setRegister (lhs.of_reg v_2915) v_11142;
      pure ()
    pat_end;
    pattern fun (v_2918 : Mem) (v_2919 : reg (bv 256)) => do
      v_11144 <- evaluateAddress v_2918;
      v_11145 <- load v_11144 32;
      setRegister (lhs.of_reg v_2919) v_11145;
      pure ()
    pat_end
