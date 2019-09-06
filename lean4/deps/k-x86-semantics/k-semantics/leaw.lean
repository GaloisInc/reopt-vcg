def leaw1 : instruction :=
  definst "leaw" $ do
    pattern fun (v_3116 : Mem) (v_3117 : reg (bv 16)) => do
      v_7243 <- evaluateAddress v_3116;
      setRegister (lhs.of_reg v_3117) (extract v_7243 48 64);
      pure ()
    pat_end
