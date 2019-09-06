def cmovngew1 : instruction :=
  definst "cmovngew" $ do
    pattern fun (v_2986 : reg (bv 16)) (v_2987 : reg (bv 16)) => do
      v_4712 <- getRegister sf;
      v_4713 <- getRegister of;
      v_4716 <- getRegister v_2986;
      v_4717 <- getRegister v_2987;
      setRegister (lhs.of_reg v_2987) (mux (notBool_ (eq v_4712 v_4713)) v_4716 v_4717);
      pure ()
    pat_end;
    pattern fun (v_2982 : Mem) (v_2983 : reg (bv 16)) => do
      v_8048 <- getRegister sf;
      v_8049 <- getRegister of;
      v_8052 <- evaluateAddress v_2982;
      v_8053 <- load v_8052 2;
      v_8054 <- getRegister v_2983;
      setRegister (lhs.of_reg v_2983) (mux (notBool_ (eq v_8048 v_8049)) v_8053 v_8054);
      pure ()
    pat_end
