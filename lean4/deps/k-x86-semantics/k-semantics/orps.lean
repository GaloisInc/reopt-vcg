def orps1 : instruction :=
  definst "orps" $ do
    pattern fun (v_2987 : reg (bv 128)) (v_2988 : reg (bv 128)) => do
      v_4818 <- getRegister v_2988;
      v_4819 <- getRegister v_2987;
      setRegister (lhs.of_reg v_2988) (bv_or v_4818 v_4819);
      pure ()
    pat_end;
    pattern fun (v_2982 : Mem) (v_2983 : reg (bv 128)) => do
      v_9153 <- getRegister v_2983;
      v_9154 <- evaluateAddress v_2982;
      v_9155 <- load v_9154 16;
      setRegister (lhs.of_reg v_2983) (bv_or v_9153 v_9155);
      pure ()
    pat_end
