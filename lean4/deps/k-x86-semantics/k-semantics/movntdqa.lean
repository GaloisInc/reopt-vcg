def movntdqa1 : instruction :=
  definst "movntdqa" $ do
    pattern fun (v_2537 : Mem) (v_2538 : reg (bv 128)) => do
      v_8876 <- evaluateAddress v_2537;
      v_8877 <- load v_8876 16;
      setRegister (lhs.of_reg v_2538) v_8877;
      pure ()
    pat_end
