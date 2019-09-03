def leaq1 : instruction :=
  definst "leaq" $ do
    pattern fun (v_3021 : Mem) (v_3022 : reg (bv 64)) => do
      v_7393 <- evaluateAddress v_3021;
      setRegister (lhs.of_reg v_3022) v_7393;
      pure ()
    pat_end
