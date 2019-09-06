def pmaxud1 : instruction :=
  definst "pmaxud" $ do
    pattern fun (v_2675 : reg (bv 128)) (v_2676 : reg (bv 128)) => do
      v_5003 <- getRegister v_2676;
      v_5004 <- eval (extract v_5003 0 32);
      v_5005 <- getRegister v_2675;
      v_5006 <- eval (extract v_5005 0 32);
      v_5009 <- eval (extract v_5003 32 64);
      v_5010 <- eval (extract v_5005 32 64);
      v_5013 <- eval (extract v_5003 64 96);
      v_5014 <- eval (extract v_5005 64 96);
      v_5017 <- eval (extract v_5003 96 128);
      v_5018 <- eval (extract v_5005 96 128);
      setRegister (lhs.of_reg v_2676) (concat (mux (ugt v_5004 v_5006) v_5004 v_5006) (concat (mux (ugt v_5009 v_5010) v_5009 v_5010) (concat (mux (ugt v_5013 v_5014) v_5013 v_5014) (mux (ugt v_5017 v_5018) v_5017 v_5018))));
      pure ()
    pat_end;
    pattern fun (v_2671 : Mem) (v_2672 : reg (bv 128)) => do
      v_11844 <- getRegister v_2672;
      v_11845 <- eval (extract v_11844 0 32);
      v_11846 <- evaluateAddress v_2671;
      v_11847 <- load v_11846 16;
      v_11848 <- eval (extract v_11847 0 32);
      v_11851 <- eval (extract v_11844 32 64);
      v_11852 <- eval (extract v_11847 32 64);
      v_11855 <- eval (extract v_11844 64 96);
      v_11856 <- eval (extract v_11847 64 96);
      v_11859 <- eval (extract v_11844 96 128);
      v_11860 <- eval (extract v_11847 96 128);
      setRegister (lhs.of_reg v_2672) (concat (mux (ugt v_11845 v_11848) v_11845 v_11848) (concat (mux (ugt v_11851 v_11852) v_11851 v_11852) (concat (mux (ugt v_11855 v_11856) v_11855 v_11856) (mux (ugt v_11859 v_11860) v_11859 v_11860))));
      pure ()
    pat_end
