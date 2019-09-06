def vmovntdqa1 : instruction :=
  definst "vmovntdqa" $ do
    pattern fun (v_2990 : Mem) (v_2991 : reg (bv 128)) => do
      v_10229 <- evaluateAddress v_2990;
      v_10230 <- load v_10229 16;
      setRegister (lhs.of_reg v_2991) v_10230;
      pure ()
    pat_end;
    pattern fun (v_2994 : Mem) (v_2995 : reg (bv 256)) => do
      v_10232 <- evaluateAddress v_2994;
      v_10233 <- load v_10232 32;
      setRegister (lhs.of_reg v_2995) v_10233;
      pure ()
    pat_end
