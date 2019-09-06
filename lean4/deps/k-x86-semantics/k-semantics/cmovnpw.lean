def cmovnpw1 : instruction :=
  definst "cmovnpw" $ do
    pattern fun (v_3121 : reg (bv 16)) (v_3122 : reg (bv 16)) => do
      v_4891 <- getRegister pf;
      v_4893 <- getRegister v_3121;
      v_4894 <- getRegister v_3122;
      setRegister (lhs.of_reg v_3122) (mux (notBool_ v_4891) v_4893 v_4894);
      pure ()
    pat_end;
    pattern fun (v_3117 : Mem) (v_3118 : reg (bv 16)) => do
      v_8182 <- getRegister pf;
      v_8184 <- evaluateAddress v_3117;
      v_8185 <- load v_8184 2;
      v_8186 <- getRegister v_3118;
      setRegister (lhs.of_reg v_3118) (mux (notBool_ v_8182) v_8185 v_8186);
      pure ()
    pat_end
