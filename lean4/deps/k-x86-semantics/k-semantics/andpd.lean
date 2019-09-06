def andpd1 : instruction :=
  definst "andpd" $ do
    pattern fun (v_2911 : reg (bv 128)) (v_2912 : reg (bv 128)) => do
      v_5297 <- getRegister v_2912;
      v_5298 <- getRegister v_2911;
      setRegister (lhs.of_reg v_2912) (bv_and v_5297 v_5298);
      pure ()
    pat_end;
    pattern fun (v_2910 : Mem) (v_2907 : reg (bv 128)) => do
      v_9020 <- getRegister v_2907;
      v_9021 <- evaluateAddress v_2910;
      v_9022 <- load v_9021 16;
      setRegister (lhs.of_reg v_2907) (bv_and v_9020 v_9022);
      pure ()
    pat_end
