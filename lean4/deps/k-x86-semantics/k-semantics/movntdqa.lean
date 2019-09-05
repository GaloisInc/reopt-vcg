def movntdqa1 : instruction :=
  definst "movntdqa" $ do
    pattern fun (v_2600 : Mem) (v_2601 : reg (bv 128)) => do
      v_8719 <- evaluateAddress v_2600;
      v_8720 <- load v_8719 16;
      setRegister (lhs.of_reg v_2601) v_8720;
      pure ()
    pat_end
