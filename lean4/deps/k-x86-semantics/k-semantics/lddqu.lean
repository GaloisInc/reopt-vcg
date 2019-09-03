def lddqu1 : instruction :=
  definst "lddqu" $ do
    pattern fun (v_3013 : Mem) (v_3014 : reg (bv 128)) => do
      v_8915 <- evaluateAddress v_3013;
      v_8916 <- load v_8915 16;
      setRegister (lhs.of_reg v_3014) v_8916;
      pure ()
    pat_end
