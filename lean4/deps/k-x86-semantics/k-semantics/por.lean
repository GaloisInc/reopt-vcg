def por1 : instruction :=
  definst "por" $ do
    pattern fun (v_2935 : reg (bv 128)) (v_2936 : reg (bv 128)) => do
      v_6446 <- getRegister v_2936;
      v_6447 <- getRegister v_2935;
      setRegister (lhs.of_reg v_2936) (bv_or v_6446 v_6447);
      pure ()
    pat_end;
    pattern fun (v_2932 : Mem) (v_2931 : reg (bv 128)) => do
      v_13180 <- getRegister v_2931;
      v_13181 <- evaluateAddress v_2932;
      v_13182 <- load v_13181 16;
      setRegister (lhs.of_reg v_2931) (bv_or v_13180 v_13182);
      pure ()
    pat_end
