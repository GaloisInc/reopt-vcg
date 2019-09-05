def leaw1 : instruction :=
  definst "leaw" $ do
    pattern fun (v_3089 : Mem) (v_3090 : reg (bv 16)) => do
      v_7227 <- evaluateAddress v_3089;
      setRegister (lhs.of_reg v_3090) (extract v_7227 48 64);
      pure ()
    pat_end
