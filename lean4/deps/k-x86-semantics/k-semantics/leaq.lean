def leaq1 : instruction :=
  definst "leaq" $ do
    pattern fun (v_3032 : Mem) (v_3033 : reg (bv 64)) => do
      v_7690 <- evaluateAddress v_3032;
      setRegister (lhs.of_reg v_3033) v_7690;
      pure ()
    pat_end
