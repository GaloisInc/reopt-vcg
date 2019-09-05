def leaq1 : instruction :=
  definst "leaq" $ do
    pattern fun (v_3085 : Mem) (v_3086 : reg (bv 64)) => do
      v_7225 <- evaluateAddress v_3085;
      setRegister (lhs.of_reg v_3086) v_7225;
      pure ()
    pat_end
