def movapd1 : instruction :=
  definst "movapd" $ do
    pattern fun (v_3218 : reg (bv 128)) (v_3219 : reg (bv 128)) => do
      v_5733 <- getRegister v_3218;
      setRegister (lhs.of_reg v_3219) v_5733;
      pure ()
    pat_end;
    pattern fun (v_3211 : reg (bv 128)) (v_3210 : Mem) => do
      v_7509 <- evaluateAddress v_3210;
      v_7510 <- getRegister v_3211;
      store v_7509 v_7510 16;
      pure ()
    pat_end;
    pattern fun (v_3214 : Mem) (v_3215 : reg (bv 128)) => do
      v_8956 <- evaluateAddress v_3214;
      v_8957 <- load v_8956 16;
      setRegister (lhs.of_reg v_3215) v_8957;
      pure ()
    pat_end
