def cmovnow1 : instruction :=
  definst "cmovnow" $ do
    pattern fun (v_3094 : reg (bv 16)) (v_3095 : reg (bv 16)) => do
      v_4861 <- getRegister of;
      v_4863 <- getRegister v_3094;
      v_4864 <- getRegister v_3095;
      setRegister (lhs.of_reg v_3095) (mux (notBool_ v_4861) v_4863 v_4864);
      pure ()
    pat_end;
    pattern fun (v_3090 : Mem) (v_3091 : reg (bv 16)) => do
      v_8161 <- getRegister of;
      v_8163 <- evaluateAddress v_3090;
      v_8164 <- load v_8163 2;
      v_8165 <- getRegister v_3091;
      setRegister (lhs.of_reg v_3091) (mux (notBool_ v_8161) v_8164 v_8165);
      pure ()
    pat_end
