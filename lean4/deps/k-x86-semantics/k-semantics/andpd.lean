def andpd1 : instruction :=
  definst "andpd" $ do
    pattern fun (v_2887 : reg (bv 128)) (v_2888 : reg (bv 128)) => do
      v_5416 <- getRegister v_2888;
      v_5417 <- getRegister v_2887;
      setRegister (lhs.of_reg v_2888) (bv_and v_5416 v_5417);
      pure ()
    pat_end;
    pattern fun (v_2882 : Mem) (v_2883 : reg (bv 128)) => do
      v_9196 <- getRegister v_2883;
      v_9197 <- evaluateAddress v_2882;
      v_9198 <- load v_9197 16;
      setRegister (lhs.of_reg v_2883) (bv_and v_9196 v_9198);
      pure ()
    pat_end
