def vpor1 : instruction :=
  definst "vpor" $ do
    pattern fun (v_2959 : Mem) (v_2957 : reg (bv 128)) (v_2958 : reg (bv 128)) => do
      v_14190 <- getRegister v_2957;
      v_14191 <- evaluateAddress v_2959;
      v_14192 <- load v_14191 16;
      setRegister (lhs.of_reg v_2958) (bv_or v_14190 v_14192);
      pure ()
    pat_end;
    pattern fun (v_2968 : Mem) (v_2969 : reg (bv 256)) (v_2970 : reg (bv 256)) => do
      v_14195 <- getRegister v_2969;
      v_14196 <- evaluateAddress v_2968;
      v_14197 <- load v_14196 32;
      setRegister (lhs.of_reg v_2970) (bv_or v_14195 v_14197);
      pure ()
    pat_end
