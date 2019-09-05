def movapd1 : instruction :=
  definst "movapd" $ do
    pattern fun (v_3192 : reg (bv 128)) (v_3193 : reg (bv 128)) => do
      v_5717 <- getRegister v_3192;
      setRegister (lhs.of_reg v_3193) v_5717;
      pure ()
    pat_end;
    pattern fun (v_3184 : reg (bv 128)) (v_3183 : Mem) => do
      v_7493 <- evaluateAddress v_3183;
      v_7494 <- getRegister v_3184;
      store v_7493 v_7494 16;
      pure ()
    pat_end;
    pattern fun (v_3187 : Mem) (v_3188 : reg (bv 128)) => do
      v_8946 <- evaluateAddress v_3187;
      v_8947 <- load v_8946 16;
      setRegister (lhs.of_reg v_3188) v_8947;
      pure ()
    pat_end
