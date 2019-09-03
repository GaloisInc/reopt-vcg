def leaw1 : instruction :=
  definst "leaw" $ do
    pattern fun (v_3025 : Mem) (v_3026 : reg (bv 16)) => do
      v_7395 <- evaluateAddress v_3025;
      setRegister (lhs.of_reg v_3026) (extract v_7395 48 64);
      pure ()
    pat_end
