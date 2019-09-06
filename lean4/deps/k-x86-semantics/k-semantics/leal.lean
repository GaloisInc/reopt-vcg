def leal1 : instruction :=
  definst "leal" $ do
    pattern fun (v_3108 : Mem) (v_3109 : reg (bv 32)) => do
      v_7238 <- evaluateAddress v_3108;
      setRegister (lhs.of_reg v_3109) (extract v_7238 32 64);
      pure ()
    pat_end
