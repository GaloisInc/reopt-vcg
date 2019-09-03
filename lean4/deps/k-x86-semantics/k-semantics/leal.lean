def leal1 : instruction :=
  definst "leal" $ do
    pattern fun (v_3028 : Mem) (v_3029 : reg (bv 32)) => do
      v_7687 <- evaluateAddress v_3028;
      setRegister (lhs.of_reg v_3029) (extract v_7687 32 64);
      pure ()
    pat_end
