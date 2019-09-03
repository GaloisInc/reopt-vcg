def movapd1 : instruction :=
  definst "movapd" $ do
    pattern fun (v_3140 : reg (bv 128)) (v_3141 : reg (bv 128)) => do
      v_6182 <- getRegister v_3140;
      setRegister (lhs.of_reg v_3141) v_6182;
      pure ()
    pat_end;
    pattern fun (v_3132 : reg (bv 128)) (v_3130 : Mem) => do
      v_7958 <- evaluateAddress v_3130;
      v_7959 <- getRegister v_3132;
      store v_7958 v_7959 16;
      pure ()
    pat_end;
    pattern fun (v_3134 : Mem) (v_3136 : reg (bv 128)) => do
      v_9896 <- evaluateAddress v_3134;
      v_9897 <- load v_9896 16;
      setRegister (lhs.of_reg v_3136) v_9897;
      pure ()
    pat_end
