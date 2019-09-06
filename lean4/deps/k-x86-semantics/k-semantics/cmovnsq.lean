def cmovnsq1 : instruction :=
  definst "cmovnsq" $ do
    pattern fun (v_3155 : reg (bv 64)) (v_3156 : reg (bv 64)) => do
      v_4921 <- getRegister sf;
      v_4923 <- getRegister v_3155;
      v_4924 <- getRegister v_3156;
      setRegister (lhs.of_reg v_3156) (mux (notBool_ v_4921) v_4923 v_4924);
      pure ()
    pat_end;
    pattern fun (v_3147 : Mem) (v_3148 : reg (bv 64)) => do
      v_8198 <- getRegister sf;
      v_8200 <- evaluateAddress v_3147;
      v_8201 <- load v_8200 8;
      v_8202 <- getRegister v_3148;
      setRegister (lhs.of_reg v_3148) (mux (notBool_ v_8198) v_8201 v_8202);
      pure ()
    pat_end
