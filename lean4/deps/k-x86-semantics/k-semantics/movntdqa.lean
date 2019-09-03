def movntdqa1 : instruction :=
  definst "movntdqa" $ do
    pattern fun (v_2550 : Mem) (v_2551 : reg (bv 128)) => do
      v_8855 <- evaluateAddress v_2550;
      v_8856 <- load v_8855 16;
      setRegister (lhs.of_reg v_2551) v_8856;
      pure ()
    pat_end
