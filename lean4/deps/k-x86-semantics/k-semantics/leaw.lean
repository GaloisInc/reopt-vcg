def leaw1 : instruction :=
  definst "leaw" $ do
    pattern fun (v_3036 : Mem) (v_3038 : reg (bv 16)) => do
      v_7692 <- evaluateAddress v_3036;
      setRegister (lhs.of_reg v_3038) (extract v_7692 48 64);
      pure ()
    pat_end
