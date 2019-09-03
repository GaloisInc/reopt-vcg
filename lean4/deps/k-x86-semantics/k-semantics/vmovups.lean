def vmovups1 : instruction :=
  definst "vmovups" $ do
    pattern fun (v_3046 : Mem) (v_3047 : reg (bv 128)) => do
      v_10414 <- evaluateAddress v_3046;
      v_10415 <- load v_10414 16;
      setRegister (lhs.of_reg v_3047) v_10415;
      pure ()
    pat_end;
    pattern fun (v_3055 : Mem) (v_3056 : reg (bv 256)) => do
      v_10417 <- evaluateAddress v_3055;
      v_10418 <- load v_10417 32;
      setRegister (lhs.of_reg v_3056) v_10418;
      pure ()
    pat_end;
    pattern fun (v_3039 : reg (bv 128)) (v_3038 : Mem) => do
      v_12785 <- evaluateAddress v_3038;
      v_12786 <- getRegister v_3039;
      store v_12785 v_12786 16;
      pure ()
    pat_end;
    pattern fun (v_3043 : reg (bv 256)) (v_3042 : Mem) => do
      v_12788 <- evaluateAddress v_3042;
      v_12789 <- getRegister v_3043;
      store v_12788 v_12789 32;
      pure ()
    pat_end
