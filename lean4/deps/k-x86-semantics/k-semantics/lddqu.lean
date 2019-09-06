def lddqu1 : instruction :=
  definst "lddqu" $ do
    pattern fun (v_3104 : Mem) (v_3105 : reg (bv 128)) => do
      v_8647 <- evaluateAddress v_3104;
      v_8648 <- load v_8647 16;
      setRegister (lhs.of_reg v_3105) v_8648;
      pure ()
    pat_end
