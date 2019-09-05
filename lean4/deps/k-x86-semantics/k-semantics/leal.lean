def leal1 : instruction :=
  definst "leal" $ do
    pattern fun (v_3081 : Mem) (v_3082 : reg (bv 32)) => do
      v_7222 <- evaluateAddress v_3081;
      setRegister (lhs.of_reg v_3082) (extract v_7222 32 64);
      pure ()
    pat_end
