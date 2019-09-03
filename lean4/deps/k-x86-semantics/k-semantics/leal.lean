def leal1 : instruction :=
  definst "leal" $ do
    pattern fun (v_3017 : Mem) (v_3018 : reg (bv 32)) => do
      v_7390 <- evaluateAddress v_3017;
      setRegister (lhs.of_reg v_3018) (extract v_7390 32 64);
      pure ()
    pat_end
