def leaq1 : instruction :=
  definst "leaq" $ do
    pattern fun (v_3112 : Mem) (v_3113 : reg (bv 64)) => do
      v_7241 <- evaluateAddress v_3112;
      setRegister (lhs.of_reg v_3113) v_7241;
      pure ()
    pat_end
