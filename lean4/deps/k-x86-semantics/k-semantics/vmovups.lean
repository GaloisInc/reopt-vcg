def vmovups1 : instruction :=
  definst "vmovups" $ do
    pattern fun (v_3059 : Mem) (v_3060 : reg (bv 128)) => do
      v_11219 <- evaluateAddress v_3059;
      v_11220 <- load v_11219 16;
      setRegister (lhs.of_reg v_3060) v_11220;
      pure ()
    pat_end;
    pattern fun (v_3068 : Mem) (v_3069 : reg (bv 256)) => do
      v_11222 <- evaluateAddress v_3068;
      v_11223 <- load v_11222 32;
      setRegister (lhs.of_reg v_3069) v_11223;
      pure ()
    pat_end;
    pattern fun (v_3052 : reg (bv 128)) (v_3051 : Mem) => do
      v_13662 <- evaluateAddress v_3051;
      v_13663 <- getRegister v_3052;
      store v_13662 v_13663 16;
      pure ()
    pat_end;
    pattern fun (v_3056 : reg (bv 256)) (v_3055 : Mem) => do
      v_13665 <- evaluateAddress v_3055;
      v_13666 <- getRegister v_3056;
      store v_13665 v_13666 32;
      pure ()
    pat_end
