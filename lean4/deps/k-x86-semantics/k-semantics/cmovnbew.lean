def cmovnbew1 : instruction :=
  definst "cmovnbew" $ do
    pattern fun (v_2878 : reg (bv 16)) (v_2879 : reg (bv 16)) => do
      v_4585 <- getRegister cf;
      v_4587 <- getRegister zf;
      v_4590 <- getRegister v_2878;
      v_4591 <- getRegister v_2879;
      setRegister (lhs.of_reg v_2879) (mux (bit_and (notBool_ v_4585) (notBool_ v_4587)) v_4590 v_4591);
      pure ()
    pat_end;
    pattern fun (v_2874 : Mem) (v_2875 : reg (bv 16)) => do
      v_7957 <- getRegister cf;
      v_7959 <- getRegister zf;
      v_7962 <- evaluateAddress v_2874;
      v_7963 <- load v_7962 2;
      v_7964 <- getRegister v_2875;
      setRegister (lhs.of_reg v_2875) (mux (bit_and (notBool_ v_7957) (notBool_ v_7959)) v_7963 v_7964);
      pure ()
    pat_end
