def vmovntdqa1 : instruction :=
  definst "vmovntdqa" $ do
    pattern fun (v_2901 : Mem) (v_2902 : reg (bv 128)) => do
      v_10336 <- evaluateAddress v_2901;
      v_10337 <- load v_10336 16;
      setRegister (lhs.of_reg v_2902) v_10337;
      pure ()
    pat_end;
    pattern fun (v_2905 : Mem) (v_2906 : reg (bv 256)) => do
      v_10339 <- evaluateAddress v_2905;
      v_10340 <- load v_10339 32;
      setRegister (lhs.of_reg v_2906) v_10340;
      pure ()
    pat_end
