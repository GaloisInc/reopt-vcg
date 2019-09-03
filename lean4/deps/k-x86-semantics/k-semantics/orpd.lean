def orpd1 : instruction :=
  definst "orpd" $ do
    pattern fun (v_2990 : reg (bv 128)) (v_2991 : reg (bv 128)) => do
      v_4899 <- getRegister v_2991;
      v_4900 <- getRegister v_2990;
      setRegister (lhs.of_reg v_2991) (bv_or v_4899 v_4900);
      pure ()
    pat_end;
    pattern fun (v_2986 : Mem) (v_2987 : reg (bv 128)) => do
      v_9223 <- getRegister v_2987;
      v_9224 <- evaluateAddress v_2986;
      v_9225 <- load v_9224 16;
      setRegister (lhs.of_reg v_2987) (bv_or v_9223 v_9225);
      pure ()
    pat_end
