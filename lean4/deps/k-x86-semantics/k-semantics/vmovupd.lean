def vmovupd1 : instruction :=
  definst "vmovupd" $ do
    pattern fun (v_3084 : Mem) (v_3085 : reg (bv 128)) => do
      v_10272 <- evaluateAddress v_3084;
      v_10273 <- load v_10272 16;
      setRegister (lhs.of_reg v_3085) v_10273;
      pure ()
    pat_end;
    pattern fun (v_3093 : Mem) (v_3094 : reg (bv 256)) => do
      v_10275 <- evaluateAddress v_3093;
      v_10276 <- load v_10275 32;
      setRegister (lhs.of_reg v_3094) v_10276;
      pure ()
    pat_end;
    pattern fun (v_3077 : reg (bv 128)) (v_3076 : Mem) => do
      v_12459 <- evaluateAddress v_3076;
      v_12460 <- getRegister v_3077;
      store v_12459 v_12460 16;
      pure ()
    pat_end;
    pattern fun (v_3081 : reg (bv 256)) (v_3080 : Mem) => do
      v_12462 <- evaluateAddress v_3080;
      v_12463 <- getRegister v_3081;
      store v_12462 v_12463 32;
      pure ()
    pat_end
