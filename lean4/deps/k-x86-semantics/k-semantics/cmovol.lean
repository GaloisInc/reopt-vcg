def cmovol1 : instruction :=
  definst "cmovol" $ do
    pattern fun (v_3211 : reg (bv 32)) (v_3212 : reg (bv 32)) => do
      v_4976 <- getRegister of;
      v_4977 <- getRegister v_3211;
      v_4978 <- getRegister v_3212;
      setRegister (lhs.of_reg v_3212) (mux v_4976 v_4977 v_4978);
      pure ()
    pat_end;
    pattern fun (v_3204 : Mem) (v_3207 : reg (bv 32)) => do
      v_8234 <- getRegister of;
      v_8235 <- evaluateAddress v_3204;
      v_8236 <- load v_8235 4;
      v_8237 <- getRegister v_3207;
      setRegister (lhs.of_reg v_3207) (mux v_8234 v_8236 v_8237);
      pure ()
    pat_end
