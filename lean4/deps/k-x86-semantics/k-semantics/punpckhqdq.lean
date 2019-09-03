def punpckhqdq1 : instruction :=
  definst "punpckhqdq" $ do
    pattern fun (v_3180 : reg (bv 128)) (v_3181 : reg (bv 128)) => do
      v_9097 <- getRegister v_3180;
      v_9099 <- getRegister v_3181;
      setRegister (lhs.of_reg v_3181) (concat (extract v_9097 0 64) (extract v_9099 0 64));
      pure ()
    pat_end;
    pattern fun (v_3175 : Mem) (v_3176 : reg (bv 128)) => do
      v_15981 <- evaluateAddress v_3175;
      v_15982 <- load v_15981 16;
      v_15984 <- getRegister v_3176;
      setRegister (lhs.of_reg v_3176) (concat (extract v_15982 0 64) (extract v_15984 0 64));
      pure ()
    pat_end
