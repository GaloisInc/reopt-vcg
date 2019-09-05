def lddqu1 : instruction :=
  definst "lddqu" $ do
    pattern fun (v_3077 : Mem) (v_3078 : reg (bv 128)) => do
      v_8637 <- evaluateAddress v_3077;
      v_8638 <- load v_8637 16;
      setRegister (lhs.of_reg v_3078) v_8638;
      pure ()
    pat_end
