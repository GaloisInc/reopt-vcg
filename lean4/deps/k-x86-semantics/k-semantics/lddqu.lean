def lddqu1 : instruction :=
  definst "lddqu" $ do
    pattern fun (v_3024 : Mem) (v_3026 : reg (bv 128)) => do
      v_9505 <- evaluateAddress v_3024;
      v_9506 <- load v_9505 16;
      setRegister (lhs.of_reg v_3026) v_9506;
      pure ()
    pat_end
