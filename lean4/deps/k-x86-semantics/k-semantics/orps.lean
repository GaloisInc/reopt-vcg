def orps1 : instruction :=
  definst "orps" $ do
    pattern fun (v_3050 : reg (bv 128)) (v_3051 : reg (bv 128)) => do
      v_4823 <- getRegister v_3051;
      v_4824 <- getRegister v_3050;
      setRegister (lhs.of_reg v_3051) (bv_or v_4823 v_4824);
      pure ()
    pat_end;
    pattern fun (v_3045 : Mem) (v_3046 : reg (bv 128)) => do
      v_8992 <- getRegister v_3046;
      v_8993 <- evaluateAddress v_3045;
      v_8994 <- load v_8993 16;
      setRegister (lhs.of_reg v_3046) (bv_or v_8992 v_8994);
      pure ()
    pat_end
