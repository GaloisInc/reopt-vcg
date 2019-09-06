def movntdqa1 : instruction :=
  definst "movntdqa" $ do
    pattern fun (v_2626 : Mem) (v_2627 : reg (bv 128)) => do
      v_8746 <- evaluateAddress v_2626;
      v_8747 <- load v_8746 16;
      setRegister (lhs.of_reg v_2627) v_8747;
      pure ()
    pat_end
